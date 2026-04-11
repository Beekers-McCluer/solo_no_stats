/*

++++++++++++++++++++ SOLO BASE TARGET ++++++++++++++++++++
 - Most basic model. Highly configurable, but no stats.
 - RTC hardware entirely unused.


 NOTES ============================================================================================================

 FastLED provides several 'preset' palettes: RainbowColors_p, RainbowStripeColors_p,
 OceanColors_p, CloudColors_p, LavaColors_p, ForestColors_p, and PartyColors_p.

LED 5v (ws2812b)
LED control = D4

SD 3.3v
SD CS = D5
SD MOSI = D23
SD CLK = D18
SD MISO = D19

ADXL345 3.3v
ADXL345 SDA = D21
ADXL345 SCL = D22

DS3231M 5v
DS3231M SDA = D21
DS3231M SCL = D22
*/

#include <Arduino.h>
#include <WiFi.h>               // 802.11
#include <NetworkClient.h>      // webserver
#include <AsyncTCP.h>           // webserver
#include <ESPAsyncWebServer.h>  // webserver
#include <WiFiClientSecure.h>   // for updates (github)
#include <HTTPClient.h>         // for updates (github)
#include <HTTPUpdate.h>         // for updates (firmware install)
#include "esp_task_wdt.h"       // for updates (disable watchdog)
#include <Arduino_JSON.h>       // for passing data to webserver
#include <Wire.h>               // for pixel
#include <FastLED.h>            // ws2812b pixel
#include "FS.h"                 // handle files -- needed for sd card/LittleFS
#include "SD.h"                 // interface with sd card
#include "SPI.h"                // for sd card
#include "LittleFS.h"           // interface with esp32 nvram
#include <SparkFun_ADXL345.h>   // SparkFun ADXL345 Library
#include <ESPmDNS.h>            // *.local dns name
#include "index_html.h"
#include "settings_html.h"


#define LED_PIN 4  // WS2812B control pin
#define NUM_LEDS 12
#define LED_TYPE WS2812B
#define COLOR_ORDER GRB
CRGB leds[NUM_LEDS];
#define UPDATES_PER_SECOND 100
#define FORMAT_LITTLEFS_IF_FAILED true
#define fileNAMEonly (strrchr(__FILE__, '/') ? strrchr(__FILE__, '/') + 1 : strrchr(__FILE__, '\\') ? strrchr(__FILE__, '\\') + 1 \
                                                                                                    : __FILE__)  //from: https://stackoverflow.com/questions/8487986/file-macro-shows-full-path
const char compileDate[] PROGMEM = __DATE__;                                                                     //  built-in function in C++ makes text string: Jun 29 2023
const char compileTime[] PROGMEM = __TIME__;                                                                     //  built-in function in C++ makes text string: 10:04:18


//--- Global variables for system update ---//
const char* current_version = "SNS-0.0.2";
bool updateAvailable = false;
String newBinUrl = "";

//-- WS2812B
CRGBPalette16 currentPalette;
TBlendType currentBlending;

uint8_t bpm = 500;
uint8_t selectedHue = 0;
uint8_t selectedSaturation = 255;
uint8_t minBrightness = 1;  // NEW: Minimum glow (0-255)
uint8_t scaledMax;          // used to remap brighness to 8bit for pulsing effects
uint8_t pulseVal;           // used for pulsing effects

CRGB getCRGBFromName(const char* name) {
  // CHSV(Hue, Saturation, Brightness/Value)
  // Hue: 0-255 (Rainbow), Sat: 0-255 (0=White), Val: 0-255
  if (strcmp(name, "red") == 0) return CHSV(0, 255, 255);
  if (strcmp(name, "orange") == 0) return CHSV(32, 255, 255);
  if (strcmp(name, "yellow") == 0) return CHSV(64, 255, 255);
  if (strcmp(name, "green") == 0) return CHSV(96, 255, 255);
  if (strcmp(name, "aqua") == 0) return CHSV(128, 255, 255);
  if (strcmp(name, "blue") == 0) return CHSV(160, 255, 255);
  if (strcmp(name, "purple") == 0) return CHSV(192, 255, 255);
  if (strcmp(name, "pink") == 0) return CHSV(224, 255, 255);
  // White: Saturation = 0 makes it white regardless of Hue
  if (strcmp(name, "white") == 0) return CHSV(0, 0, 255);
  return CRGB::Black;  // Default if no match
}

CRGBPalette16 getPaletteFromName(const char* name) {
  if (strcmp(name, "RainbowColors_p") == 0) return RainbowColors_p;
  if (strcmp(name, "OceanColors_p") == 0) return OceanColors_p;
  if (strcmp(name, "CloudColors_p") == 0) return CloudColors_p;
  if (strcmp(name, "LavaColors_p") == 0) return LavaColors_p;
  if (strcmp(name, "ForestColors_p") == 0) return ForestColors_p;
  if (strcmp(name, "PartyColors_p") == 0) return PartyColors_p;
  return RainbowColors_p;  // Default
}

//--- ADXL345 3 - 5.5V
ADXL345 adxl = ADXL345();  // I2C COMMUNICATION for Accellerometer
uint8_t cardType;          // sd card

unsigned long hobbsMeter = 0;  // 1 = 6mins
unsigned long hobbsHits = 0;   // lifetime hits
unsigned long hobbsMeterMillis = 0;
unsigned long autoResetMillis = 0;
unsigned long targetAutoDrawMillis = 0;  // for autoDraw timer
unsigned long currentMillis;
unsigned long timerMicros;
unsigned long countdownMillis;
unsigned long randomMillis;
unsigned long drawMillis;
unsigned long drawWarningMillis;

int startIndex;                      // used to truncate times on website when showMicrosecondsToggle is true
String buffer_const_char = "";       // buffer for SD/LittleFS reads. needs to be here, used in various read functions.
unsigned long buffer_unsigned_long;  // SD/LittleFS ul read buffer

bool resetState = false;  // used to auto-reset
bool targetAutoDraw_hold = true;
bool targetWarmUpState = false;
bool testState = false;
bool FLAG_SD_mountFail = false;
bool FLAG_toggleLight = false;
bool FLAG_showStartupLight = false;
bool FLAG_autoDrawFirstShot = true;
bool freeSpaceError = false;
bool FLAG_AP_mode = false;
bool DEBUG_FLAG_hitLightOn = false;
bool DEBUG_FLAG_drawLightOn = false;
bool DEBUG_FLAG_startupLightOn = false;
bool FLAG_drawWarning = false;
bool startUpdateNow = false;

volatile boolean startDraw = false;
volatile boolean targetActiveState = false;
volatile boolean targetTimedOut = false;
volatile boolean hitFlashState = false;
volatile boolean firstShotState = true;
volatile boolean drawFlashState = false;
uint8_t randomSecond;  // uint8_t = 0-255

//--- used for dashboard display ---//
char buffer_shotTime_micros[9];  // number of digits + 1 for EOF
char buffer_previousResult[9];   // number of digits + 1 for EOF
char buffer_currentResult[9];    // number of digits + 1 for EOF
char allButLast3[9];             // 9 = 8 digit = 99.999999 seconds
char last3[9];
const char* whiff = "No Hit";
const char* pend = "Pending";
const char* hitNoTime = "No Time";
const char* test = "Test";
const char* test_exp = "Test Expired";
const char* na = "N/A";
char BRIGHTNESS_ascii[4];
char THRESHOLD_ascii[4];

String lightDuration;  // for time between draw button and target light
String val;            // buffer used for trimming microseconds from web stats

bool coinFlip;  // for demo mode

//=========================================================================================================================//
//-------------------------------------------------- targetConfig struct --------------------------------------------------//
//=========================================================================================================================//

//--- These are all default values
typedef struct struct_target_config {
  // 0 = off, 1 = on
  bool showMicrosecondsToggle = 1;
  bool targetAutoDrawToggle = 0;
  bool drawWarningSoundToggle = 0;
  bool autoResetToggle = 1;
  bool startupLightToggle = 1;
  bool homeNetworkToggle = 1;
  bool openNetworkToggle = 0;  // old logic that's currently only used in backend. needs rooted out.
  bool simulationToggle = 0;
  bool drawWarningLightToggle = 1;
  char LED_startupLight[32] = "OceanColors_p";       // user defined palette
  uint8_t LED_startupLightSpeed = 5;                 // user defined speed
  char LED_drawWarningLight[32] = "red";             // user defined palette
  uint8_t LED_drawWarningLightSpeed = 10;            // user defined speed +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ functionality not yet implemented. Will be used with auto-draw.
  char LED_drawLight[32] = "PartyColors_p";          // user defined palette
  uint8_t LED_drawLightSpeed = 5;                    // user defined speed
//  char LED_hitInvalid[32] = "red";                   // user defined palette
//  uint8_t LED_hitInvalidSpeed = 0;                   // user defined speed
  char LED_hit0s[32] = "red";                      // user defined palette
  uint8_t LED_hit0sSpeed = 10;                     // user defined speed
  char LED_hit100s[32] = "red";                      // user defined palette
  uint8_t LED_hit100sSpeed = 10;                     // user defined speed
  char LED_hit200s[32] = "red";                      // user defined palette
  uint8_t LED_hit200sSpeed = 10;                     // user defined speed
  char LED_hit300s[32] = "red";                      // user defined palette
  uint8_t LED_hit300sSpeed = 10;                     // user defined speed
  char LED_hit400s[32] = "blue";                     // user defined palette
  uint8_t LED_hit400sSpeed = 10;                     // user defined speed
  char LED_hit500s[32] = "green";                    // user defined palette
  uint8_t LED_hit500sSpeed = 10;                     // user defined speed
  char LED_hit600s[32] = "purple";                   // user defined palette
  uint8_t LED_hit600sSpeed = 10;                     // user defined speed
  char LED_hit700s[32] = "aqua";                     // user defined palette
  uint8_t LED_hit700sSpeed = 10;                     // user defined speed
  char LED_hit800s[32] = "white";                    // user defined palette
  uint8_t LED_hit800sSpeed = 10;                     // user defined speed
  char LED_hit900s[32] = "orange";                   // user defined palette
  uint8_t LED_hit900sSpeed = 10;                     // user defined speed
  char LED_hit1000s[32] = "yellow";                  // user defined palette
  uint8_t LED_hit1000sSpeed = 10;                    // user defined speed
  char LED_hit1100s[32] = "pink";                    // user defined palette
  uint8_t LED_hit1100sSpeed = 10;                    // user defined speed
  char LED_hit1200s[32] = "red";                     // user defined palette
  uint8_t LED_hit1200sSpeed = 10;                    // user defined speed
  char LED_hit1300s[32] = "ForestColors_p";                     // user defined palette
  uint8_t LED_hit1300sSpeed = 10;                    // user defined speed
  char LED_hit1400s[32] = "OceanColors_p";                     // user defined palette
  uint8_t LED_hit1400sSpeed = 10;                    // user defined speed
  char LED_hit1500plus[32] = "CloudColors_p";                     // user defined palette
  uint8_t LED_hit1500plusSpeed = 10;                    // user defined speed
  char LED_palette[32];                              // for displayChurn
  uint8_t LED_speed;                                 // for displayChurn
  unsigned long drawWait = 1;                        // delay after pushing button.
  unsigned long drawSecMax = 5;                      // draw time window
  unsigned long TARGET_TIMEOUT = 3;                  // seconds before reporting NO HIT
  unsigned long THRESHOLD = 100;                     // originally 50. 0-255. 62.5 mg per increment. 255 = 16G = max
  unsigned long BRIGHTNESS = 30;                     // ws2812b 60mA full bright white. 20mA per chan. 100 max
  unsigned long RESET_SECS = 10;                     // # of secs after draw light to auto-reset
  unsigned long AUTODRAW_SECS = 5;                   // # of secs after reset to start new draw sequence
  char OPEN_SSID[32] = "ScruffyNet_AP";
  char HOME_SSID[32] = "KeplerNet";
  char HOME_PASS[64] = "KeplerNetWyfy";
  char dns_name[32] = "target";
} struct_target_config;
struct_target_config targetConfig;

unsigned long shotTime_micros;

AsyncWebServer server(80);
AsyncWebSocket ws("/ws");  // for sliders

String message = "";  // for sliders
String sliderValue1 = BRIGHTNESS_ascii;
String sliderValue2 = THRESHOLD_ascii;

//Json Variable to Hold Slider Values
JSONVar sliderValues;  // hold slider values

// Prototype declarations
void reset_target();
void settle_target_miss();
void settle_target_hit();
void set_target();
void broadcastStats();
void sendSettings(AsyncWebSocketClient* client);
void handleWebSocketMessage(AsyncWebSocketClient* client, void* arg, uint8_t* data, size_t len);
void onEvent(AsyncWebSocket* server, AsyncWebSocketClient* client, AwsEventType type, void* arg, uint8_t* data, size_t len);
void FillLEDsFromPaletteColors(CRGBPalette16 palette, uint8_t colorIndex, uint8_t brightness);
void notifyClients(String sliderValues);
void checkForUpdates();
void write_unsigned_long(fs::FS& fs, const char* path, unsigned long value);
void write_String(fs::FS& fs, const char* path, const char* message);
void savePalette(fs::FS& fs, const char* path, const char* data, size_t len);
bool loadPalette(fs::FS& fs, const char* path, unsigned char* buffer, size_t maxLen);
unsigned long read_ul(fs::FS& fs, const char* path);
String read_String(fs::FS& fs, const char* path, size_t maxLen = 1500);

void update_progress(int cur, int total) {
  static int lastPercent = -1;
  int percent = (100 * cur) / total;
  if (percent != lastPercent) {
    lastPercent = percent;
    // Broadcast progress to all clients
    ws.textAll("ota_progress:" + String(percent));
    yield();
    delay(5);
    Serial.printf("Progress: %d%%\n", percent);
  }
}

//--- Check for Updates ---//
void checkForUpdates() {
  Serial.println("+++++++++++++++ checkForUpdates() called +++++++++++++++");
  WiFiClientSecure client;
  client.setInsecure(); 
  HTTPClient http;
  
  // 1. Declare the variables at the top of the function
  int httpCode = 0;


  // Replace with your actual GitHub RAW link
  if (http.begin(client, "https://raw.githubusercontent.com/Beekers-McCluer/solo_no_stats/refs/heads/main/version.json")) {
    
    // 2. Assign the value during the GET request
    httpCode = http.GET(); 

    if (httpCode == HTTP_CODE_OK) {
      String payload = http.getString();
      
      // Use your Arduino_JSON.h syntax
      JSONVar doc = JSON.parse(payload);

      if (JSON.typeof(doc) == "undefined") {
        Serial.println("Parsing version.json failed!");
        return;
      }

      // 3. Compare versions
      if (doc.hasOwnProperty("version")) {
        const char* remoteVersion = (const char*)doc["version"];
        // Explicitly compare and set the flag
        if (String(remoteVersion) != String(current_version)) {
          updateAvailable = true;
          newBinUrl = (const char*)doc["bin_url"];
          Serial.println("New version found!");
        } else {
          // Version matches, so no update is available
          updateAvailable = false;
          newBinUrl = "";
          Serial.println("System is up to date.");
        }
        // Notify clients of the current status
        ws.textAll("update_status:" + String(updateAvailable ? "true" : "false"));
      }
    } else {
      Serial.printf("HTTP GET failed, error: %s\n", http.errorToString(httpCode).c_str());
    }
    http.end();
  }
}

//--- Hit Flash logic ---//
void processHitVisuals(const char* colorName, uint8_t speed) {
  // 1. Calculate brightness first so it's available for the whole function
  uint8_t scaledMax = map(targetConfig.BRIGHTNESS, 0, 100, 0, 255);
  // 2. Check for speed 0 (Solid ON)
  if (speed == 0) {
    CRGB color = getCRGBFromName(colorName);
    // Use the scaledMax here to ensure brightness setting is respected
    fill_solid(leds, NUM_LEDS, color);
    FastLED.setBrightness(scaledMax);
    FastLED.show();
    return;
  }
  // 3. Handle Palettes
  if (strstr(colorName, "Colors_p") != NULL) {
    CRGBPalette16 palette = getPaletteFromName(colorName);
    static uint8_t startIndex = 0;
    startIndex += speed;
    FillLEDsFromPaletteColors(palette, startIndex, scaledMax);
  }
  // 4. Handle Solid Hue Pulse
  else {
    CRGB color = getCRGBFromName(colorName);
    CHSV hsv = rgb2hsv_approximate(color);
    uint8_t bpm = map(speed, 1, 10, 30, 200);
    /* 
       beatsin8(bpm, low, high, phase_offset, time_offset)
       Setting the 5th parameter (time_offset) to 64 shifts the sine wave 
       90 degrees so it starts at the PEAK (scaledMax).
    */
    uint8_t pulseVal = beatsin8(bpm, 1, scaledMax, 0, 64);
    fill_solid(leds, NUM_LEDS, CHSV(hsv.hue, hsv.sat, pulseVal));
  }
  FastLED.show();
}

//--- used to send stats to individual users when settings.html page is loaded ---//
void sendSettings(AsyncWebSocketClient* client) {


  Serial.println("+++ Sending settings to client");
  String json = "{";
  json.reserve(4096);

  // --- 2. Sliders & G-Force ---
  json += "\"slider1\":\"" + String(targetConfig.BRIGHTNESS) + "\",";
  json += "\"sliderValue1\":\"" + String(targetConfig.BRIGHTNESS) + "\",";
  json += "\"slider2\":\"" + String(targetConfig.THRESHOLD) + "\",";
  json += "\"sliderValue2\":\"" + String(targetConfig.THRESHOLD) + "\",";
  json += "\"gforce\":\"" + String(((targetConfig.THRESHOLD + 1) * 0.0625), 3) + "\",";

  // --- 3. Dropdowns & Configuration ---
  json += "\"reset_secs_val\":\"" + String(targetConfig.RESET_SECS) + "\",";
  json += "\"autoDraw_secs_val\":\"" + String(targetConfig.AUTODRAW_SECS) + "\",";
  json += "\"reset_secs\":\"" + String(targetConfig.RESET_SECS) + "\",";  // sets default value for drop down
  json += "\"autoDraw_secs\":\"" + String(targetConfig.AUTODRAW_SECS) + "\",";

  // --- 4. Draw Sequence Settings ---
  json += "\"drawWait\":\"" + String(targetConfig.drawWait) + "\",";
  json += "\"drawSecMax\":\"" + String(targetConfig.drawSecMax) + "\",";
  json += "\"drawWait_LBL\":\"" + String(targetConfig.drawWait) + "\",";
  json += "\"drawSecMax_LBL\":\"" + String(targetConfig.drawSecMax) + "\",";

  // --- 5. Toggles (IDs 1-13) ---
  json += "\"1\":\"" + String(targetConfig.showMicrosecondsToggle ? "1" : "0") + "\",";
  json += "\"4\":\"" + String(targetConfig.startupLightToggle ? "1" : "0") + "\",";
  json += "\"5\":\"" + String(targetConfig.drawWarningSoundToggle ? "1" : "0") + "\",";
  json += "\"6\":\"" + String(targetConfig.targetAutoDrawToggle ? "1" : "0") + "\",";
  json += "\"7\":\"" + String(targetConfig.autoResetToggle ? "1" : "0") + "\",";
  json += "\"10\":\"" + String(targetConfig.simulationToggle ? "1" : "0") + "\",";
  json += "\"12\":\"" + String(FLAG_toggleLight ? "1" : "0") + "\",";
  json += "\"14\":\"" + String(targetConfig.drawWarningLightToggle ? "1" : "0") + "\",";


  // --- 6. Network Labels ---
  json += "\"OPEN_SSID_LBL\":\"" + String(targetConfig.OPEN_SSID) + "\",";
  json += "\"HOME_SSID_LBL\":\"" + String(targetConfig.HOME_SSID) + "\",";
  json += "\"HOME_PASS_LBL\":\"" + String(targetConfig.HOME_PASS) + "\",";
  json += "\"DNS_LBL\":\"" + String(targetConfig.dns_name) + ".local\",";

  // --- 7. Hobbs and Ranges ---
  char hBuf[12];
  dtostrf((float)hobbsMeter / 10.0, 6, 1, hBuf);
  String hStr = String(hBuf);
  hStr.trim();
  json += "\"HOBBS_METER\":\"" + hStr + "\",";
  json += "\"HOBBS_HITS\":\"" + String(hobbsHits) + "\",";

  // --- 8. LED Palette Styles & Speeds ---
  json += "\"LED_startupLight\":\"" + String(targetConfig.LED_startupLight) + "\",";
  json += "\"LED_startupLightSpeed\":\"" + String(targetConfig.LED_startupLightSpeed) + "\",";
  json += "\"LED_drawWarningLight\":\"" + String(targetConfig.LED_drawWarningLight) + "\",";
  json += "\"LED_drawLight\":\"" + String(targetConfig.LED_drawLight) + "\",";
  json += "\"LED_drawLightSpeed\":\"" + String(targetConfig.LED_drawLightSpeed) + "\",";
  json += "\"LED_hit0s\":\"" + String(targetConfig.LED_hit0s) + "\",";
  json += "\"LED_hit0sSpeed\":\"" + String(targetConfig.LED_hit0sSpeed) + "\",";
  json += "\"LED_hit100s\":\"" + String(targetConfig.LED_hit100s) + "\",";
  json += "\"LED_hit100sSpeed\":\"" + String(targetConfig.LED_hit100sSpeed) + "\",";
  json += "\"LED_hit200s\":\"" + String(targetConfig.LED_hit200s) + "\",";
  json += "\"LED_hit200sSpeed\":\"" + String(targetConfig.LED_hit200sSpeed) + "\",";
  json += "\"LED_hit300s\":\"" + String(targetConfig.LED_hit300s) + "\",";
  json += "\"LED_hit300sSpeed\":\"" + String(targetConfig.LED_hit300sSpeed) + "\",";
  json += "\"LED_hit400s\":\"" + String(targetConfig.LED_hit400s) + "\",";
  json += "\"LED_hit400sSpeed\":\"" + String(targetConfig.LED_hit400sSpeed) + "\",";
  json += "\"LED_hit500s\":\"" + String(targetConfig.LED_hit500s) + "\",";
  json += "\"LED_hit500sSpeed\":\"" + String(targetConfig.LED_hit500sSpeed) + "\",";
  json += "\"LED_hit600s\":\"" + String(targetConfig.LED_hit600s) + "\",";
  json += "\"LED_hit600sSpeed\":\"" + String(targetConfig.LED_hit600sSpeed) + "\",";
  json += "\"LED_hit700s\":\"" + String(targetConfig.LED_hit700s) + "\",";
  json += "\"LED_hit700sSpeed\":\"" + String(targetConfig.LED_hit700sSpeed) + "\",";
  json += "\"LED_hit800s\":\"" + String(targetConfig.LED_hit800s) + "\",";
  json += "\"LED_hit800sSpeed\":\"" + String(targetConfig.LED_hit800sSpeed) + "\",";
  json += "\"LED_hit900s\":\"" + String(targetConfig.LED_hit900s) + "\",";
  json += "\"LED_hit900sSpeed\":\"" + String(targetConfig.LED_hit900sSpeed) + "\",";
  json += "\"LED_hit1000s\":\"" + String(targetConfig.LED_hit1000s) + "\",";
  json += "\"LED_hit1000sSpeed\":\"" + String(targetConfig.LED_hit1000sSpeed) + "\",";
  json += "\"LED_hit1100s\":\"" + String(targetConfig.LED_hit1100s) + "\",";
  json += "\"LED_hit1100sSpeed\":\"" + String(targetConfig.LED_hit1100sSpeed) + "\",";
  json += "\"LED_hit1200s\":\"" + String(targetConfig.LED_hit1200s) + "\",";
  json += "\"LED_hit1200sSpeed\":\"" + String(targetConfig.LED_hit1200sSpeed) + "\",";
  json += "\"LED_hit1300s\":\"" + String(targetConfig.LED_hit1300s) + "\",";
  json += "\"LED_hit1300sSpeed\":\"" + String(targetConfig.LED_hit1300sSpeed) + "\",";
  json += "\"LED_hit1400s\":\"" + String(targetConfig.LED_hit1400s) + "\",";
  json += "\"LED_hit1400sSpeed\":\"" + String(targetConfig.LED_hit1400sSpeed) + "\",";
  json += "\"LED_hit1500plus\":\"" + String(targetConfig.LED_hit1500plus) + "\",";
  json += "\"LED_hit1500plusSpeed\":\"" + String(targetConfig.LED_hit1500plusSpeed) + "\",";
  json += "\"firmware_ver\":\"" + String(current_version) + "\","; 
  json += "\"updateAvailable\":" + String(updateAvailable ? "true" : "false");              // end without comma
  json += "}";                                                                              // close json string.

  if (client != NULL && client->status() == WS_CONNECTED) {
    client->text(json);
  }
  Serial.print("+++++ Sent target settings: ");
  Serial.println(json);
}

//--- used to push stats to everyone. same as above. ---//
void broadcastStats() {
  Serial.println("++++++++++++++++++++ broadcastStats() called ++++++++++++++++++++");
  String json = "{";
  json.reserve(1600);

  json += "\"FLAG_AP\":\"" + String(FLAG_AP_mode ? "SETUP MODE " : "") + "\",";                                    // if flag is true, show text
  json += "\"FLAG_SD\":\"" + String(FLAG_SD_mountFail ? "SD " : "") + "\",";                               // if flag is true, show text
  json += "\"autoDrawActive\":\"" + String(targetConfig.targetAutoDrawToggle ? "Auto Draw " : "") + "\",";  // if toggle is on, show auto draw is active
  if (!targetConfig.targetAutoDrawToggle) {
    json += "\"autoResetActive\":\"" + String(targetConfig.autoResetToggle ? "Auto Reset " : "") + "\",";  // if toggle is on, show auto reset is active
  }
  json += "\"lightDuration\":\"" + String(lightDuration) + "\",";
  json += "\"allButLast3\":\"" + String(allButLast3) + "\",";
  json += "\"12\":\"" + String(FLAG_toggleLight ? "1" : "0") + "\",";  // Announcer's light toggle position
  // 1. Handle Microseconds Toggle
  json += "\"last3\":\"" + String(targetConfig.showMicrosecondsToggle ? last3 : "") + "\""; // end with no trailing comma
  json += "}";
  // 5. Broadcast to all connected clients
  ws.textAll(json);
  Serial.print("+++++ Sent all connected clients: ");
  Serial.println(json);
}

void handleWebSocketMessage(AsyncWebSocketClient* client, void* arg, uint8_t* data, size_t len) {
  data[len] = 0;
  String message = (char*)data;
  if (message == "getSettingsData") {
    sendSettings(client);
  } else if (message == "getStats") {
    broadcastStats();
  }

  AwsFrameInfo* info = (AwsFrameInfo*)arg;
  if (info->final && info->index == 0 && info->len == len && info->opcode == WS_TEXT) {
    // --- Slider 1: Brightness ---
    if (message.indexOf("1s") >= 0) {
      sliderValue1 = message.substring(2);
      targetConfig.BRIGHTNESS = sliderValue1.toInt();
      FastLED.setBrightness(targetConfig.BRIGHTNESS);
      scaledMax = map(targetConfig.BRIGHTNESS, 0, 100, 0, 255);
      write_unsigned_long(LittleFS, "/BRIGHTNESS.dat", targetConfig.BRIGHTNESS);
    }

    // --- Slider 2: Threshold ---
    else if (message.indexOf("2s") >= 0) {
      sliderValue2 = message.substring(2);
      targetConfig.THRESHOLD = sliderValue2.toInt();
      write_unsigned_long(LittleFS, "/THRESHOLD.dat", targetConfig.THRESHOLD);
    }

    // --- GITHUB OTA UPDATE ---
    else if (message == "trigger_ota_github") {
      if (updateAvailable && newBinUrl != "") {
        startUpdateNow = true; // Set flag to trigger in loop()
        ws.textAll("ota_starting"); 
      }
    }



    // --- DRAW BUTTON ---
    else if (message == "draw") {
      Serial.println("+++++ Draw button press");
      set_target();
    }

    // --- RESET BUTTON ---
    else if (message == "reset") {
      Serial.println("+++++ Reset button press");
      reset_target();
    }

    // --- TEST BUTTON ---
    else if (message == "test") {
      Serial.println("+++++ Test button press");
      testState = true;
      set_target();
    }

    // --- Generic Dropdown Settings and Text Input Fields work ---
    else if (message.startsWith("setting:")) {
      int firstColon = message.indexOf(':');
      int lastColon = message.lastIndexOf(':');
      String id = message.substring(firstColon + 1, lastColon);
      String val = message.substring(lastColon + 1);

      if (id == "OPEN_SSID") {
        strncpy(targetConfig.OPEN_SSID, val.c_str(), sizeof(targetConfig.OPEN_SSID) - 1);
        targetConfig.OPEN_SSID[sizeof(targetConfig.OPEN_SSID) - 1] = '\0';
        Serial.printf("Setting %s updated to: %s\n", id.c_str(), val.c_str());
        write_String(LittleFS, "/OPEN_SSID.dat", targetConfig.OPEN_SSID);

      } else if (id == "HOME_SSID") {
        strncpy(targetConfig.HOME_SSID, val.c_str(), sizeof(targetConfig.HOME_SSID) - 1);
        targetConfig.HOME_SSID[sizeof(targetConfig.HOME_SSID) - 1] = '\0';
        Serial.printf("Setting %s updated to: %s\n", id.c_str(), val.c_str());
        write_String(LittleFS, "/HOME_SSID.dat", targetConfig.HOME_SSID);

      } else if (id == "HOME_PASS") {
        strncpy(targetConfig.HOME_PASS, val.c_str(), sizeof(targetConfig.HOME_PASS) - 1);
        targetConfig.HOME_PASS[sizeof(targetConfig.HOME_PASS) - 1] = '\0';
        Serial.printf("Setting %s updated to: %s\n", id.c_str(), val.c_str());
        write_String(LittleFS, "/HOME_PASS.dat", targetConfig.HOME_PASS);

      } else if (id == "TARGET_TIMEOUT") {
        targetConfig.TARGET_TIMEOUT = val.toInt();
        Serial.printf("Setting %s updated to: %s\n", id.c_str(), val.c_str());
        write_unsigned_long(LittleFS, "/TARGET_TIMEOUT.dat", targetConfig.TARGET_TIMEOUT);

      } else if (id == "dns_name") {
        strncpy(targetConfig.dns_name, val.c_str(), sizeof(targetConfig.dns_name) - 1);
        targetConfig.dns_name[sizeof(targetConfig.dns_name) - 1] = '\0';
        Serial.printf("Setting %s updated to: %s\n", id.c_str(), val.c_str());
        write_String(LittleFS, "/dns_name.dat", targetConfig.dns_name);

      } else if (id == "drawSecMax") {
        targetConfig.drawSecMax = val.toInt();
        Serial.printf("Setting %s updated to: %s\n", id.c_str(), val.c_str());
        write_unsigned_long(LittleFS, "/drawSecMax.dat", targetConfig.drawSecMax);

      } else if (id == "reset_secs") {
        targetConfig.RESET_SECS = val.toInt();
        Serial.printf("Setting %s updated to: %s\n", id.c_str(), val.c_str());
        write_unsigned_long(LittleFS, "/RESET_SECS.dat", targetConfig.RESET_SECS);

      } else if (id == "autoDraw_secs") {
        targetConfig.AUTODRAW_SECS = val.toInt();
        Serial.printf("Setting %s updated to: %s\n", id.c_str(), val.c_str());
        write_unsigned_long(LittleFS, "/AUTODRAW_SECS.dat", targetConfig.AUTODRAW_SECS);

      } else if (id == "drawWait") {
        targetConfig.drawWait = val.toInt();
        Serial.printf("Setting %s updated to: %s\n", id.c_str(), val.c_str());
        write_unsigned_long(LittleFS, "/drawWait.dat", targetConfig.drawWait);

      } else if (id == "drawSecMax") {
        targetConfig.drawSecMax = val.toInt();
        Serial.printf("Setting %s updated to: %s\n", id.c_str(), val.c_str());
        write_unsigned_long(LittleFS, "/drawSecMax.dat", targetConfig.drawSecMax);

      } else if (id == "LED_startupLight") {
        strncpy(targetConfig.LED_startupLight, val.c_str(), sizeof(targetConfig.LED_startupLight) - 1);
        targetConfig.LED_startupLight[sizeof(targetConfig.LED_startupLight) - 1] = '\0';
        Serial.printf("Setting %s updated to: %s\n", id.c_str(), val.c_str());
        savePalette(LittleFS, "/LED_startupLight.dat", targetConfig.LED_startupLight, strlen(targetConfig.LED_startupLight));

      } else if (id == "LED_startupLightSpeed") {
        targetConfig.LED_startupLightSpeed = val.toInt();
        Serial.printf("Setting %s updated to: %s\n", id.c_str(), val.c_str());
        write_unsigned_long(LittleFS, "/LED_startupLightSpeed.dat", targetConfig.LED_startupLightSpeed);

      } else if (id == "LED_drawWarningLight") {
        strncpy(targetConfig.LED_drawWarningLight, val.c_str(), sizeof(targetConfig.LED_drawWarningLight) - 1);
        targetConfig.LED_drawWarningLight[sizeof(targetConfig.LED_drawWarningLight) - 1] = '\0';
        Serial.printf("Setting %s updated to: %s\n", id.c_str(), val.c_str());
        savePalette(LittleFS, "/LED_drawWarningLight.dat", targetConfig.LED_drawWarningLight, strlen(targetConfig.LED_drawWarningLight));

      } else if (id == "LED_drawLight") {
        strncpy(targetConfig.LED_drawLight, val.c_str(), sizeof(targetConfig.LED_drawLight) - 1);
        targetConfig.LED_drawLight[sizeof(targetConfig.LED_drawLight) - 1] = '\0';
        Serial.printf("Setting %s updated to: %s\n", id.c_str(), val.c_str());
        savePalette(LittleFS, "/LED_drawLight.dat", targetConfig.LED_drawLight, strlen(targetConfig.LED_drawLight));

      } else if (id == "LED_drawLightSpeed") {
        targetConfig.LED_drawLightSpeed = val.toInt();
        Serial.printf("Setting %s updated to: %s\n", id.c_str(), val.c_str());
        write_unsigned_long(LittleFS, "/LED_drawLightSpeed.dat", targetConfig.LED_drawLightSpeed);

      } else if (id == "LED_startupLight") {
        strncpy(targetConfig.LED_startupLight, val.c_str(), sizeof(targetConfig.LED_startupLight) - 1);
        targetConfig.LED_startupLight[sizeof(targetConfig.LED_startupLight) - 1] = '\0';
        Serial.printf("Setting %s updated to: %s\n", id.c_str(), val.c_str());
        savePalette(LittleFS, "/LED_startupLight.dat", targetConfig.LED_startupLight, strlen(targetConfig.LED_startupLight));

      } else if (id == "LED_startupLightSpeed") {
        targetConfig.LED_startupLightSpeed = val.toInt();
        Serial.printf("Setting %s updated to: %s\n", id.c_str(), val.c_str());
        write_unsigned_long(LittleFS, "/LED_startupLightSpeed.dat", targetConfig.LED_startupLightSpeed);

      } else if (id == "LED_hit0s") {
        strncpy(targetConfig.LED_hit0s, val.c_str(), sizeof(targetConfig.LED_hit0s) - 1);
        targetConfig.LED_hit0s[sizeof(targetConfig.LED_hit0s) - 1] = '\0';
        Serial.printf("Setting %s updated to: %s\n", id.c_str(), val.c_str());
        savePalette(LittleFS, "/LED_hit0s.dat", targetConfig.LED_hit0s, strlen(targetConfig.LED_hit0s));

      } else if (id == "LED_hit0sSpeed") {
        targetConfig.LED_hit0sSpeed = val.toInt();
        Serial.printf("Setting %s updated to: %s\n", id.c_str(), val.c_str());
        write_unsigned_long(LittleFS, "/LED_hit0sSpeed.dat", targetConfig.LED_hit0sSpeed);

      } else if (id == "LED_hit100s") {
        strncpy(targetConfig.LED_hit100s, val.c_str(), sizeof(targetConfig.LED_hit100s) - 1);
        targetConfig.LED_hit100s[sizeof(targetConfig.LED_hit100s) - 1] = '\0';
        Serial.printf("Setting %s updated to: %s\n", id.c_str(), val.c_str());
        savePalette(LittleFS, "/LED_hit100s.dat", targetConfig.LED_hit100s, strlen(targetConfig.LED_hit100s));

      } else if (id == "LED_hit100sSpeed") {
        targetConfig.LED_hit100sSpeed = val.toInt();
        Serial.printf("Setting %s updated to: %s\n", id.c_str(), val.c_str());
        write_unsigned_long(LittleFS, "/LED_hit100sSpeed.dat", targetConfig.LED_hit100sSpeed);

      } else if (id == "LED_hit200s") {
        strncpy(targetConfig.LED_hit200s, val.c_str(), sizeof(targetConfig.LED_hit200s) - 1);
        targetConfig.LED_hit200s[sizeof(targetConfig.LED_hit200s) - 1] = '\0';
        Serial.printf("Setting %s updated to: %s\n", id.c_str(), val.c_str());
        savePalette(LittleFS, "/LED_hit200s.dat", targetConfig.LED_hit200s, strlen(targetConfig.LED_hit200s));

      } else if (id == "LED_hit200sSpeed") {
        targetConfig.LED_hit200sSpeed = val.toInt();
        Serial.printf("Setting %s updated to: %s\n", id.c_str(), val.c_str());
        write_unsigned_long(LittleFS, "/LED_hit200sSpeed.dat", targetConfig.LED_hit200sSpeed);

      } else if (id == "LED_hit300s") {
        strncpy(targetConfig.LED_hit300s, val.c_str(), sizeof(targetConfig.LED_hit300s) - 1);
        targetConfig.LED_hit300s[sizeof(targetConfig.LED_hit300s) - 1] = '\0';
        Serial.printf("Setting %s updated to: %s\n", id.c_str(), val.c_str());
        savePalette(LittleFS, "/LED_hit300s.dat", targetConfig.LED_hit300s, strlen(targetConfig.LED_hit300s));

      } else if (id == "LED_hit300sSpeed") {
        targetConfig.LED_hit300sSpeed = val.toInt();
        Serial.printf("Setting %s updated to: %s\n", id.c_str(), val.c_str());
        write_unsigned_long(LittleFS, "/LED_hit300sSpeed.dat", targetConfig.LED_hit300sSpeed);

      } else if (id == "LED_hit400s") {
        strncpy(targetConfig.LED_hit400s, val.c_str(), sizeof(targetConfig.LED_hit400s) - 1);
        targetConfig.LED_hit400s[sizeof(targetConfig.LED_hit400s) - 1] = '\0';
        Serial.printf("Setting %s updated to: %s\n", id.c_str(), val.c_str());
        savePalette(LittleFS, "/LED_hit400s.dat", targetConfig.LED_hit400s, strlen(targetConfig.LED_hit400s));

      } else if (id == "LED_hit400sSpeed") {
        targetConfig.LED_hit400sSpeed = val.toInt();
        Serial.printf("Setting %s updated to: %s\n", id.c_str(), val.c_str());
        write_unsigned_long(LittleFS, "/LED_hit400sSpeed.dat", targetConfig.LED_hit400sSpeed);

      } else if (id == "LED_hit500s") {
        strncpy(targetConfig.LED_hit500s, val.c_str(), sizeof(targetConfig.LED_hit500s) - 1);
        targetConfig.LED_hit500s[sizeof(targetConfig.LED_hit500s) - 1] = '\0';
        Serial.printf("Setting %s updated to: %s\n", id.c_str(), val.c_str());
        savePalette(LittleFS, "/LED_hit500s.dat", targetConfig.LED_hit500s, strlen(targetConfig.LED_hit500s));

      } else if (id == "LED_hit500sSpeed") {
        targetConfig.LED_hit500sSpeed = val.toInt();
        Serial.printf("Setting %s updated to: %s\n", id.c_str(), val.c_str());
        write_unsigned_long(LittleFS, "/LED_hit500sSpeed.dat", targetConfig.LED_hit500sSpeed);

      } else if (id == "LED_hit600s") {
        strncpy(targetConfig.LED_hit600s, val.c_str(), sizeof(targetConfig.LED_hit600s) - 1);
        targetConfig.LED_hit600s[sizeof(targetConfig.LED_hit600s) - 1] = '\0';
        Serial.printf("Setting %s updated to: %s\n", id.c_str(), val.c_str());
        savePalette(LittleFS, "/LED_hit600s.dat", targetConfig.LED_hit600s, strlen(targetConfig.LED_hit600s));

      } else if (id == "LED_hit600sSpeed") {
        targetConfig.LED_hit600sSpeed = val.toInt();
        Serial.printf("Setting %s updated to: %s\n", id.c_str(), val.c_str());
        write_unsigned_long(LittleFS, "/LED_hit600sSpeed.dat", targetConfig.LED_hit600sSpeed);

      } else if (id == "LED_hit700s") {
        strncpy(targetConfig.LED_hit700s, val.c_str(), sizeof(targetConfig.LED_hit700s) - 1);
        targetConfig.LED_hit700s[sizeof(targetConfig.LED_hit700s) - 1] = '\0';
        Serial.printf("Setting %s updated to: %s\n", id.c_str(), val.c_str());
        savePalette(LittleFS, "/LED_hit700s.dat", targetConfig.LED_hit700s, strlen(targetConfig.LED_hit700s));

      } else if (id == "LED_hit700sSpeed") {
        targetConfig.LED_hit700sSpeed = val.toInt();
        Serial.printf("Setting %s updated to: %s\n", id.c_str(), val.c_str());
        write_unsigned_long(LittleFS, "/LED_hit700sSpeed.dat", targetConfig.LED_hit700sSpeed);

      } else if (id == "LED_hit800s") {
        strncpy(targetConfig.LED_hit800s, val.c_str(), sizeof(targetConfig.LED_hit800s) - 1);
        targetConfig.LED_hit800s[sizeof(targetConfig.LED_hit800s) - 1] = '\0';
        Serial.printf("Setting %s updated to: %s\n", id.c_str(), val.c_str());
        savePalette(LittleFS, "/LED_hit800s.dat", targetConfig.LED_hit800s, strlen(targetConfig.LED_hit800s));

      } else if (id == "LED_hit800sSpeed") {
        targetConfig.LED_hit800sSpeed = val.toInt();
        Serial.printf("Setting %s updated to: %s\n", id.c_str(), val.c_str());
        write_unsigned_long(LittleFS, "/LED_hit800sSpeed.dat", targetConfig.LED_hit800sSpeed);

      } else if (id == "LED_hit900s") {
        strncpy(targetConfig.LED_hit900s, val.c_str(), sizeof(targetConfig.LED_hit900s) - 1);
        targetConfig.LED_hit900s[sizeof(targetConfig.LED_hit900s) - 1] = '\0';
        Serial.printf("Setting %s updated to: %s\n", id.c_str(), val.c_str());
        savePalette(LittleFS, "/LED_hit900s.dat", targetConfig.LED_hit900s, strlen(targetConfig.LED_hit900s));

      } else if (id == "LED_hit900sSpeed") {
        targetConfig.LED_hit900sSpeed = val.toInt();
        Serial.printf("Setting %s updated to: %s\n", id.c_str(), val.c_str());
        write_unsigned_long(LittleFS, "/LED_hit900sSpeed.dat", targetConfig.LED_hit900sSpeed);

      } else if (id == "LED_hit1000s") {
        strncpy(targetConfig.LED_hit1000s, val.c_str(), sizeof(targetConfig.LED_hit1000s) - 1);
        targetConfig.LED_hit1000s[sizeof(targetConfig.LED_hit1000s) - 1] = '\0';
        Serial.printf("Setting %s updated to: %s\n", id.c_str(), val.c_str());
        savePalette(LittleFS, "/LED_hit1000s.dat", targetConfig.LED_hit1000s, strlen(targetConfig.LED_hit1000s));

      } else if (id == "LED_hit1000sSpeed") {
        targetConfig.LED_hit1000sSpeed = val.toInt();
        Serial.printf("Setting %s updated to: %s\n", id.c_str(), val.c_str());
        write_unsigned_long(LittleFS, "/LED_hit1000sSpeed.dat", targetConfig.LED_hit1000sSpeed);

      } else if (id == "LED_hit1100s") {
        strncpy(targetConfig.LED_hit1100s, val.c_str(), sizeof(targetConfig.LED_hit1100s) - 1);
        targetConfig.LED_hit1100s[sizeof(targetConfig.LED_hit1100s) - 1] = '\0';
        Serial.printf("Setting %s updated to: %s\n", id.c_str(), val.c_str());
        savePalette(LittleFS, "/LED_hit1100s.dat", targetConfig.LED_hit1100s, strlen(targetConfig.LED_hit1100s));

      } else if (id == "LED_hit1100sSpeed") {
        targetConfig.LED_hit1100sSpeed = val.toInt();
        Serial.printf("Setting %s updated to: %s\n", id.c_str(), val.c_str());
        write_unsigned_long(LittleFS, "/LED_hit1100sSpeed.dat", targetConfig.LED_hit1100sSpeed);

      } else if (id == "LED_hit1200s") {
        strncpy(targetConfig.LED_hit1200s, val.c_str(), sizeof(targetConfig.LED_hit1200s) - 1);
        targetConfig.LED_hit1200s[sizeof(targetConfig.LED_hit1200s) - 1] = '\0';
        Serial.printf("Setting %s updated to: %s\n", id.c_str(), val.c_str());
        savePalette(LittleFS, "/LED_hit1200s.dat", targetConfig.LED_hit1200s, strlen(targetConfig.LED_hit1200s));

      } else if (id == "LED_hit1200sSpeed") {
        targetConfig.LED_hit1200sSpeed = val.toInt();
        Serial.printf("Setting %s updated to: %s\n", id.c_str(), val.c_str());
        write_unsigned_long(LittleFS, "/LED_hit1200sSpeed.dat", targetConfig.LED_hit1200sSpeed);

      } else if (id == "LED_hit1300s") {
        strncpy(targetConfig.LED_hit1300s, val.c_str(), sizeof(targetConfig.LED_hit1300s) - 1);
        targetConfig.LED_hit1300s[sizeof(targetConfig.LED_hit1300s) - 1] = '\0';
        Serial.printf("Setting %s updated to: %s\n", id.c_str(), val.c_str());
        savePalette(LittleFS, "/LED_hit1300s.dat", targetConfig.LED_hit1300s, strlen(targetConfig.LED_hit1300s));

      } else if (id == "LED_hit1300sSpeed") {
        targetConfig.LED_hit1300sSpeed = val.toInt();
        Serial.printf("Setting %s updated to: %s\n", id.c_str(), val.c_str());
        write_unsigned_long(LittleFS, "/LED_hit1300sSpeed.dat", targetConfig.LED_hit1300sSpeed);

      } else if (id == "LED_hit1400s") {
        strncpy(targetConfig.LED_hit1400s, val.c_str(), sizeof(targetConfig.LED_hit1400s) - 1);
        targetConfig.LED_hit1400s[sizeof(targetConfig.LED_hit1400s) - 1] = '\0';
        Serial.printf("Setting %s updated to: %s\n", id.c_str(), val.c_str());
        savePalette(LittleFS, "/LED_hit1400s.dat", targetConfig.LED_hit1400s, strlen(targetConfig.LED_hit1400s));

      } else if (id == "LED_hit1400sSpeed") {
        targetConfig.LED_hit1400sSpeed = val.toInt();
        Serial.printf("Setting %s updated to: %s\n", id.c_str(), val.c_str());
        write_unsigned_long(LittleFS, "/LED_hit1400sSpeed.dat", targetConfig.LED_hit1400sSpeed);

      } else if (id == "LED_hit1500plus") {
        strncpy(targetConfig.LED_hit1500plus, val.c_str(), sizeof(targetConfig.LED_hit1500plus) - 1);
        targetConfig.LED_hit1500plus[sizeof(targetConfig.LED_hit1500plus) - 1] = '\0';
        Serial.printf("Setting %s updated to: %s\n", id.c_str(), val.c_str());
        savePalette(LittleFS, "/LED_hit1500plus.dat", targetConfig.LED_hit1500plus, strlen(targetConfig.LED_hit1500plus));

      } else if (id == "LED_hit1500plusSpeed") {
        targetConfig.LED_hit1500plusSpeed = val.toInt();
        Serial.printf("Setting %s updated to: %s\n", id.c_str(), val.c_str());
        write_unsigned_long(LittleFS, "/LED_hit1500plusSpeed.dat", targetConfig.LED_hit1500plusSpeed);
      }
    }
    // --- Toggle Switches --- do that work, crack that whip
    else if (message.startsWith("toggle:")) {
      int firstColon = message.indexOf(':');
      int lastColon = message.lastIndexOf(':');
      String toggleID = message.substring(firstColon + 1, lastColon);
      bool state = (message.substring(lastColon + 1) == "1");
      if (toggleID == "1") {
        targetConfig.showMicrosecondsToggle = state;
        Serial.printf("Microseconds Toggle (toggleID 1) set to: %d\n", state);
        write_unsigned_long(LittleFS, "/showMicrosecondsToggle.dat", state);
      }
      // --- 4: Startup Light ---
      else if (toggleID == "4") {
        targetConfig.startupLightToggle = state;
        Serial.printf("Show Startup Light Toggle (toggleID 4) set to: %d\n", state);
        write_unsigned_long(LittleFS, "/startupLightToggle.dat", state);
      }
      // --- 5: Audio Alerts ---
      else if (toggleID == "5") {
        targetConfig.drawWarningSoundToggle = state;
        Serial.printf("Audio Alert Toggle (toggleID 5) set to: %d\n", state);
        write_unsigned_long(LittleFS, "/drawWarningSoundToggle.dat", state);
      }
      // --- 6: Auto-Draw ---
      else if (toggleID == "6") {
        targetConfig.targetAutoDrawToggle = state;
        Serial.printf("Auto Draw Toggle (toggleID 6) set to: %d\n", state);
        // Logic: If Auto-Draw turns ON, Auto-Reset (7) must also turn ON
        if (state) {
          if (!targetConfig.autoResetToggle) {
            targetConfig.autoResetToggle = true;
            Serial.print("+++ Auto-Reset toggle (toggleID 7) forced true by Auto-Draw");
            write_unsigned_long(LittleFS, "/autoResetToggle.dat", 1);
          }
        }
        write_unsigned_long(LittleFS, "/targetAutoDrawToggle.dat", state);
      }
      // --- 7: Auto Reset ---
      else if (toggleID == "7") {
        if (state) {
          // ALWAYS allow turning Auto-Reset ON
          targetConfig.autoResetToggle = true;
          write_unsigned_long(LittleFS, "/autoResetToggle.dat", 1);
          Serial.println("Auto Reset (7) set to: 1");
        } else {
          // ONLY allow turning Auto-Reset OFF if Auto-Draw is also OFF
          if (!targetConfig.targetAutoDrawToggle) {
            targetConfig.autoResetToggle = false;
            write_unsigned_long(LittleFS, "/autoResetToggle.dat", 0);
            Serial.println("Auto Reset (7) set to: 0");
          } else {
            Serial.println("+++ Blocked: Cannot turn off Auto-Reset while Auto-Draw is ON");
          }
        }
      }
      // --- 10: Simulaton/Demo Mode ---
      else if (toggleID == "10") {
        targetConfig.simulationToggle = state;
        Serial.printf("Simulation/Demo Mode Toggle (toggleID 10) set to: %d\n", state);
        write_unsigned_long(LittleFS, "/simulationToggle.dat", state);
      }
      // --- 12: Toggle Light ---
      else if (toggleID == "12") {
        FLAG_showStartupLight = false;  // make sure all other lights are off
        FLAG_toggleLight = state;
        Serial.printf("Light Toggle (toggleID 12) set to: %d\n", state);
        if (!FLAG_toggleLight) {
          FastLED.clear();
          FastLED.show();
        }
      }
      // --- 14: Draw Warning Light ---
      else if (toggleID == "14") {
        targetConfig.drawWarningLightToggle = state;
        Serial.printf("Startup Light Toggle (toggleID 14) set to: %d\n", state);
        write_unsigned_long(LittleFS, "/drawWarningLightToggle.dat", targetConfig.drawWarningLightToggle);
      }
    }
  }
  sendSettings(client);
}

unsigned long read_ul(fs::FS& fs, const char* path) {
  unsigned long value = 0;
  File file = fs.open(path, FILE_READ);
  if (file) {
    if (file.size() == sizeof(value)) {
      file.read((uint8_t*)&value, sizeof(value));
      Serial.printf("File %s read successfully: %lu\n", path, value);
    } else {
      Serial.printf("unsigned long file %s size mismatch. Expected %d bytes.\n", path, sizeof(value));
    }
    file.close();
  } else {
    Serial.printf("Failed to open %s for unsigned long reading\n", path);
  }
  return value;
}

void write_unsigned_long(fs::FS& fs, const char* path, unsigned long value) {
  Serial.printf("Writing file: %s\n", path);
  File file = fs.open(path, FILE_WRITE);
  if (!file) {
    Serial.println("Failed to open file for unsigned long writing");
    return;
  }
  // Use the address of 'value' and cast it to (const uint8_t*)
  // We write exactly 4 bytes (sizeof unsigned long)
  if (file.write((const uint8_t*)&value, sizeof(value))) {
    Serial.println("- unsigned long file written");
  } else {
    Serial.println("- unsigned long write failed");
  }
  file.close();
}

String read_String(fs::FS& fs, const char* path, size_t maxLen) {
  File file = fs.open(path, FILE_READ);
  if (!file) {
    Serial.println("- read_String failed to open file");
    return "";
  }
  size_t fileSize = file.size();
  // Don't read more than your defined safety limit (1500)
  if (fileSize > maxLen) fileSize = maxLen;
  String contents = "";
  // reserve() prevents the ESP32 from "re-sizing" the string 1500 times
  if (contents.reserve(fileSize)) {
    while (file.available() && contents.length() < fileSize) {
      contents += (char)file.read();
    }
    Serial.printf("- read_String read %d characters successfully\n", contents.length());
  } else {
    Serial.println("- read_String out of memory (reserve failed)");
  }
  file.close();
  return contents;
}

void savePalette(fs::FS& fs, const char* path, const char* data, size_t len) {
  File file = fs.open(path, FILE_WRITE);
  if (!file) {
    Serial.println("- savePalette failed to open file for reading");
    return;
  }

  // We cast to (const uint8_t*) here because that's what the internal
  // file.write function requires, regardless of our input type.
  if (file.write((const uint8_t*)data, len)) {
    Serial.println("- savePalette file written");
  } else {
    Serial.println("- savePalette write failed");
  }
  file.close();
}

bool loadPalette(fs::FS& fs, const char* path, unsigned char* buffer, size_t maxLen) {  // DO NOT USE FOR NUMBERS
  File file = fs.open(path, FILE_READ);
  if (!file) {
    Serial.println("- loadPalette failed to open file for reading");
    return false;
  }
  size_t fileSize = file.size();
  // Safety Check: Don't overflow your buffer!
  size_t bytesToRead = (fileSize > maxLen) ? maxLen : fileSize;
  // Read raw bytes into the buffer
  size_t bytesRead = file.read((uint8_t*)buffer, bytesToRead);
  file.close();
  // If reading a string, ensure it is null-terminated
  if (bytesRead < maxLen) {
    buffer[bytesRead] = '\0';
  }
  Serial.printf("++++File: %s | Data: %s\n", path, (char*)buffer);
  return (bytesRead > 0);
}

void write_String(fs::FS& fs, const char* path, const char* message) {
  Serial.printf("write_String writing file: %s\n", path);
  File file = fs.open(path, FILE_WRITE);
  if (!file) {
    Serial.println("write_String failed to open file for writing");
    return;
  }
  // 1. Get the actual length of the string
  size_t len = strlen(message);
  // 2. Use file.write to save the raw bytes (just like your unsigned long function)
  // We cast to (const uint8_t*) because that is what the filesystem expects
  if (file.write((const uint8_t*)message, len)) {
    Serial.printf("- write_String file written (%d bytes)\n", len);
  } else {
    Serial.println("- write_String write failed");
  }
  file.close();
}

//--- FastLED ---//
void FillLEDsFromPaletteColors(CRGBPalette16 palette, uint8_t colorIndex, uint8_t brightness) {
  for (int i = 0; i < NUM_LEDS; ++i) {
    // Use the 'brightness' passed from your settings
    leds[i] = ColorFromPalette(palette, colorIndex, brightness, LINEARBLEND);
    colorIndex += 3;
  }
}

//---  Websocket traffic routing
void onEvent(AsyncWebSocket* server, AsyncWebSocketClient* client, AwsEventType type, void* arg, uint8_t* data, size_t len) {
  switch (type) {
    case WS_EVT_CONNECT:
      Serial.printf("WebSocket client #%u connected\n", client->id());
      sendSettings(client);
      broadcastStats();
      break;
    case WS_EVT_DISCONNECT:
      Serial.printf("WebSocket client #%u disconnected\n", client->id());
      break;
    case WS_EVT_DATA:
      handleWebSocketMessage(client, arg, data, len);
      break;
    case WS_EVT_PONG:
    case WS_EVT_ERROR:
      break;
  }
}

// Replaces placeholder with button section in web page. for toggles and settings info, etc. For web display only, no real work.
String processor(const String& var) {
  if (var == "ALIAS_LIST") {
    Serial.println("+++ calling read_String /stats/shooter_list.dat from ALIAS_LIST String processor");  // Serial monitor debugging notice
    buffer_const_char = read_String(LittleFS, "/stats/shooter_list.dat");
    String buttons = "";
    int startIndex = 0;
    int commaIndex = buffer_const_char.indexOf(',');
    while (commaIndex != -1) {
      String name = buffer_const_char.substring(startIndex, commaIndex);
      if (name.length() > 0) {
        buttons += "<option value='" + name + "'>" + name + "</option>";
      }
      startIndex = commaIndex + 1;
      commaIndex = buffer_const_char.indexOf(',', startIndex);
    }
    return buttons;
  }
  return String("");
}

void set_target() {  // determines the time when the timer will begin and handsoff with startDraw = true
  Serial.println("****************************** set_target() called ******************************");
  targetConfig.startupLightToggle = false;  // don't check, just set for faster operation.
  FastLED.clear();                          // clear any light that may be on
  delay(10);
  FastLED.show();
  if (!testState) {  // skip this if testState == true
    randomSeed(analogRead(0));
    randomSecond = (random(targetConfig.drawWait, targetConfig.drawSecMax));  // get random second between draw wait and max
    randomSeed(analogRead(0));
    randomMillis = (random(0, 11)) * 100;  // rand 0-10
  }

  //--- Build and send json String for pending shot update
  String json = "{";
  json += "\"lightDuration\":\"\",";  // block this for pending shot
  json += "\"allButLast3\":\"Pending..\",";
  json += "\"last3\":\"\"";
  json += "}";
  ws.textAll(json);  // bx json String to all connected websockets

  if (targetConfig.targetAutoDrawToggle) {
    if (FLAG_autoDrawFirstShot) {  // for initial draw in the series
      Serial.println("********** Initialshot for auto-draw **********");
      drawMillis = ((randomSecond * 1000) + randomMillis + ((targetConfig.drawWait + 3) * 1000));  // add 3 seconds to first auto-draw
      FLAG_autoDrawFirstShot = false;
    } else {
      drawMillis = ((randomSecond * 1000) + randomMillis + (targetConfig.drawWait * 1000));
    }
    targetAutoDraw_hold = true;  // hold flag decides if auto-draw should push the draw button. needs a better, non opposite day name.
  } else if (testState) {
    drawMillis = 0;
  } else {
    drawMillis = ((randomSecond * 1000) + randomMillis + (targetConfig.drawWait * 1000));
  }

  // build String for lightDuration
  float value = (float)drawMillis / 1000;  // move decimal place
  String output = String(value, 1);        // back to String
  if (testState) {
    lightDuration = "";
  } else {
    lightDuration = "Light: " + output + "s";
  }

  if (targetConfig.targetAutoDrawToggle && (targetConfig.drawWarningLightToggle || targetConfig.drawWarningSoundToggle)) {
    drawWarningMillis = drawMillis - 1000; // used to trigger Warning Light/Audio Tone, allowing 1 second for effects.
    FLAG_drawWarning = true;
  }

  Serial.print("+++++ lightDuration = ");
  Serial.println(lightDuration);
  Serial.print("+++++ randomSecond = ");
  Serial.println(randomSecond);
  Serial.print("+++++ randomMillis = ");
  Serial.println(randomMillis);
  Serial.print("+++++ targetConfig.drawWait = ");
  Serial.println(targetConfig.drawWait);
  Serial.print("+++++ drawMillis = ");
  Serial.println(drawMillis);

  startDraw = true;            // 1. Set the flag that loop() looks for
  targetActiveState = true;    // 2. Tell loop() to start checking the timer
  targetWarmUpState = true;    // and warm up
  countdownMillis = millis();  // 3. Capture the START time NOW
  Serial.println("********** end of set_target() **********");
}  // end void set_target()

void settle_target_hit() {
  Serial.println("********** settle_target_hit() called **********");

  if (!testState) {
    hobbsHits++;
    write_unsigned_long(LittleFS, "/hobbsHits.dat", hobbsHits);
  }

  // --- SAFE TIME STRING FORMATTING ---
  allButLast3[0] = '\0';
  last3[0] = '\0';
  ultoa(shotTime_micros, allButLast3, 10);
  strncpy(last3, allButLast3, sizeof(last3) - 1);
  last3[sizeof(last3) - 1] = '\0';

  int string_length = strlen(allButLast3);

  if (string_length >= 3) {
    // Populate last 3 digits
    last3[0] = last3[string_length - 3];
    last3[1] = last3[string_length - 2];
    last3[2] = last3[string_length - 1];
    last3[3] = '\0';
    // Truncate main string
    allButLast3[string_length - 3] = '\0';
  }

  // Decimal Point Insertion for 1s+ hits
  int new_len = strlen(allButLast3);
  if (string_length >= 7) {
    // Shift logic to insert '.' at index 1 (e.g. 1234 -> 1.234)
    for (int i = new_len; i > 1; i--) allButLast3[i] = allButLast3[i - 1];
    allButLast3[1] = '.';
    allButLast3[new_len + 1] = '\0';
  }

  if (testState) {
    testState = false;
  }

  if (targetConfig.autoResetToggle) {
    resetState = 1;
    autoResetMillis = millis();  // Important: reset the timer here
  }
  Serial.println("*** settle_target_hit() finished");
}

void settle_target_miss() {
  if (testState) {
    return;  // if target timeout is shorter than test expiration, don't run this function.
  }
  Serial.println("********** settle_target_miss() called **********");
  //--- Shot wind down ---//
  FastLED.clear();
  FastLED.show();

  if (targetConfig.autoResetToggle) {
    resetState = 1;  // enable reset flag
  }

  //--- update data ---//

  // ***** begin populating webserver data
  allButLast3[0] = '\0';  // clear char string
  last3[0] = '\0';        // clear char string
                          //  strcpy(allButLast3, whiff);
  strncpy(allButLast3, whiff, sizeof(allButLast3) - 1);

  Serial.println("*** settle_target_miss() finished");
}  // end void settle_target_miss()

void reset_target() {
  Serial.println("********** reset_target() called **********");
  // --- make sure all of these are OFF
  FLAG_showStartupLight = FLAG_toggleLight = resetState = targetActiveState = startDraw = hitFlashState = drawFlashState = DEBUG_FLAG_hitLightOn = DEBUG_FLAG_drawLightOn = DEBUG_FLAG_startupLightOn = false;
  Serial.println("DEBUG_FLAG's all set to false");

  // bx cleared values
  String json = "{";
  json += "\"lightDuration\":\"\",";
  json += "\"shotCount\":\"\",";
  json += "\"allButLast3\":\"\",";
  json += "\"last3\":\"\"";
  json += "}";
  ws.textAll(json);
  Serial.print("+++++ Sent all connected clients: ");
  Serial.println(json);

  FastLED.clear();  // keep at end after heavy processing (json + bx) or before with 10ms delay to allow time to finish.
  FastLED.show();
  Serial.println("********** end of reset_target");
}

void setup() {
  // Initialize Serial Monitor
  Serial.begin(115200);
  delay(3000);  // warm up
  //--- ADXL345 setup ---//
  Serial.println("***** init ADXL345");
  adxl.powerOn();                      // Power on the ADXL345
  adxl.setRangeSetting(16);            // Give the range settings
  adxl.setSpiBit(0);                   // Configure the device to be in 4 wire SPI mode when set to '0' or 3 wire SPI mode when set to 1
  adxl.setTapDetectionOnXYZ(0, 0, 1);  // Detect taps in the directions turned ON "adxl.setTapDetectionOnX(X, Y, Z);" (1 == ON, 0 == OFF)
  // Set values for what is considered a TAP and what is a DOUBLE TAP (0-255)
  adxl.setTapThreshold(targetConfig.THRESHOLD);  // 62.5 mg per increment
  adxl.setTapDuration(15);                       // 625 μs per increment
  adxl.singleTapINT(1);                          // turn on Interrupt mode 1/0. needed?
  //--- end ADXL345 setup ---//

  //--- LittleFS ---//
  // format if failed (first time running)
  if (!LittleFS.begin(FORMAT_LITTLEFS_IF_FAILED)) {
    Serial.println("LittleFS Mount Failed, formatting");
    return;
  }

  //--- SD card initialization ---//
  Serial.println("***** init SD card reader");
  if (!SD.begin(5)) {
    Serial.println("Card Mount Failed");
    FLAG_SD_mountFail = true;
  } else {
    cardType = SD.cardType();
    if (cardType == CARD_NONE) {
      Serial.println("No SD card attached");
      return;
    }
    Serial.print("SD Card Type: ");
    if (cardType == CARD_MMC) {
      Serial.println("MMC");
    } else if (cardType == CARD_SD) {
      Serial.println("SDSC");
    } else if (cardType == CARD_SDHC) {
      Serial.println("SDHC");
    } else {
      Serial.println("UNKNOWN");
    }
    uint64_t cardSize = SD.cardSize() / (1024 * 1024);
    Serial.printf("SD Card Size: %lluMB\n", cardSize);
  }
  //--- end SD card setup ---//

  //--- load data ---//

  //--- Hobbs ---//
  if (LittleFS.exists("/hobbsMeter.dat")) {
    hobbsMeter = read_ul(LittleFS, "/hobbsMeter.dat");
  } else {
    write_unsigned_long(LittleFS, "/hobbsMeter.dat", hobbsMeter);
  }
  if (LittleFS.exists("/hobbsHits.dat")) {
    hobbsHits = read_ul(LittleFS, "/hobbsHits.dat");
  } else {
    write_unsigned_long(LittleFS, "/hobbsHits.dat", hobbsHits);
  }

  //--- System Settings ---//
  if (LittleFS.exists("/OPEN_SSID.dat")) {
    String tempSSID = read_String(LittleFS, "/OPEN_SSID.dat");
    strncpy(targetConfig.OPEN_SSID, tempSSID.c_str(), sizeof(targetConfig.OPEN_SSID) - 1);
    targetConfig.OPEN_SSID[sizeof(targetConfig.OPEN_SSID) - 1] = '\0';
  } else {
    write_String(LittleFS, "/OPEN_SSID.dat", targetConfig.OPEN_SSID);
  }
  if (LittleFS.exists("/HOME_SSID.dat")) {
    String tempSSID = read_String(LittleFS, "/HOME_SSID.dat");
    strncpy(targetConfig.HOME_SSID, tempSSID.c_str(), sizeof(targetConfig.HOME_SSID) - 1);
    targetConfig.HOME_SSID[sizeof(targetConfig.HOME_SSID) - 1] = '\0';
  } else {
    write_String(LittleFS, "/HOME_SSID.dat", targetConfig.HOME_SSID);
  }
  if (LittleFS.exists("/HOME_PASS.dat")) {
    String tempPASS = read_String(LittleFS, "/HOME_PASS.dat");
    strncpy(targetConfig.HOME_PASS, tempPASS.c_str(), sizeof(targetConfig.HOME_PASS) - 1);
    targetConfig.HOME_PASS[sizeof(targetConfig.HOME_PASS) - 1] = '\0';
  } else {
    write_String(LittleFS, "/HOME_PASS.dat", targetConfig.HOME_PASS);
  }
  if (LittleFS.exists("/dns_name.dat")) {
    String tempDNS = read_String(LittleFS, "/dns_name.dat");
    strncpy(targetConfig.dns_name, tempDNS.c_str(), sizeof(targetConfig.dns_name) - 1);
    targetConfig.dns_name[sizeof(targetConfig.dns_name) - 1] = '\0';
  } else {
    write_String(LittleFS, "/dns_name.dat", targetConfig.dns_name);
  }

  //--- Draw Config
  if (LittleFS.exists("/drawWait.dat")) {
    targetConfig.drawWait = read_ul(LittleFS, "/drawWait.dat");
  } else {
    write_unsigned_long(LittleFS, "/drawWait.dat", targetConfig.drawWait);
  }
  if (LittleFS.exists("/drawSecMax.dat")) {
    targetConfig.drawSecMax = read_ul(LittleFS, "/drawSecMax.dat");
  } else {
    write_unsigned_long(LittleFS, "/drawSecMax.dat", targetConfig.drawSecMax);
  }
  if (LittleFS.exists("/TARGET_TIMEOUT.dat")) {
    targetConfig.TARGET_TIMEOUT = read_ul(LittleFS, "/TARGET_TIMEOUT.dat");
  } else {
    write_unsigned_long(LittleFS, "/TARGET_TIMEOUT.dat", targetConfig.TARGET_TIMEOUT);
  }
  if (LittleFS.exists("/THRESHOLD.dat")) {
    targetConfig.THRESHOLD = read_ul(LittleFS, "/THRESHOLD.dat");
  } else {
    write_unsigned_long(LittleFS, "/THRESHOLD.dat", targetConfig.THRESHOLD);
  }
  if (LittleFS.exists("/BRIGHTNESS.dat")) {
    targetConfig.BRIGHTNESS = read_ul(LittleFS, "/BRIGHTNESS.dat");
    scaledMax = map(targetConfig.BRIGHTNESS, 0, 100, 0, 255);  // map to 8bit for pulsing calculations
  } else {
    write_unsigned_long(LittleFS, "/BRIGHTNESS.dat", targetConfig.BRIGHTNESS);
  }
  if (LittleFS.exists("/RESET_SECS.dat")) {
    targetConfig.RESET_SECS = read_ul(LittleFS, "/RESET_SECS.dat");
  } else {
    write_unsigned_long(LittleFS, "/RESET_SECS.dat", targetConfig.RESET_SECS);
  }
  if (LittleFS.exists("/AUTODRAW_SECS.dat")) {
    targetConfig.AUTODRAW_SECS = read_ul(LittleFS, "/AUTODRAW_SECS.dat");
  } else {
    write_unsigned_long(LittleFS, "/AUTODRAW_SECS.dat", targetConfig.AUTODRAW_SECS);
  }

  //--- toggles
  if (LittleFS.exists("/showMicrosecondsToggle.dat")) {
    targetConfig.showMicrosecondsToggle = read_ul(LittleFS, "/showMicrosecondsToggle.dat");
  } else {
    write_unsigned_long(LittleFS, "/showMicrosecondsToggle.dat", targetConfig.showMicrosecondsToggle);
  }
  if (LittleFS.exists("/targetAutoDrawToggle.dat")) {
    targetConfig.targetAutoDrawToggle = read_ul(LittleFS, "/targetAutoDrawToggle.dat");
  } else {
    write_unsigned_long(LittleFS, "/targetAutoDrawToggle.dat", targetConfig.targetAutoDrawToggle);
  }
  if (LittleFS.exists("/drawWarningSoundToggle.dat")) {  // TODO: does not yet exist
    targetConfig.drawWarningSoundToggle = read_ul(LittleFS, "/drawWarningSoundToggle.dat");
  } else {
    write_unsigned_long(LittleFS, "/drawWarningSoundToggle.dat", targetConfig.drawWarningSoundToggle);
  }
  if (LittleFS.exists("/autoResetToggle.dat")) {
    targetConfig.autoResetToggle = read_ul(LittleFS, "/autoResetToggle.dat");
  } else {
    write_unsigned_long(LittleFS, "/autoResetToggle.dat", targetConfig.autoResetToggle);
  }
  if (LittleFS.exists("/startupLightToggle.dat")) {
    targetConfig.startupLightToggle = read_ul(LittleFS, "/startupLightToggle.dat");
  } else {
    write_unsigned_long(LittleFS, "/startupLightToggle.dat", targetConfig.startupLightToggle);
  }
  if (LittleFS.exists("/homeNetworkToggle.dat")) {
    targetConfig.homeNetworkToggle = read_ul(LittleFS, "/homeNetworkToggle.dat");
  } else {
    write_unsigned_long(LittleFS, "/homeNetworkToggle.dat", targetConfig.homeNetworkToggle);
  }
  if (LittleFS.exists("/simulationToggle.dat")) {
    targetConfig.simulationToggle = read_ul(LittleFS, "/simulationToggle.dat");
  } else {
    write_unsigned_long(LittleFS, "/simulationToggle.dat", targetConfig.simulationToggle);
  }

  //-- LED patterns
  if (LittleFS.exists("/LED_startupLight.dat")) {
    loadPalette(LittleFS, "/LED_startupLight.dat", (unsigned char*)targetConfig.LED_startupLight, sizeof(targetConfig.LED_startupLight));
  } else {
    size_t freeSpace = LittleFS.totalBytes() - LittleFS.usedBytes();
    if (freeSpace < 1024) {
      freeSpaceError = true;
    } else {
      size_t dataLen = strlen((const char*)targetConfig.LED_startupLight);
      savePalette(LittleFS, "/LED_startupLight.dat", targetConfig.LED_startupLight, dataLen);
    }
  }
  if (LittleFS.exists("/LED_startupLightSpeed.dat")) {
    targetConfig.LED_startupLightSpeed = read_ul(LittleFS, "/LED_startupLightSpeed.dat");
  } else {
    write_unsigned_long(LittleFS, "/LED_startupLightSpeed.dat", targetConfig.LED_startupLightSpeed);
  }
  if (LittleFS.exists("/LED_drawWarningLight.dat")) {
    loadPalette(LittleFS, "/LED_drawWarningLight.dat", (unsigned char*)targetConfig.LED_drawWarningLight, sizeof(targetConfig.LED_drawWarningLight));
  } else {
    size_t freeSpace = LittleFS.totalBytes() - LittleFS.usedBytes();
    if (freeSpace < 1024) {
      freeSpaceError = true;
    } else {
      size_t dataLen = strlen((const char*)targetConfig.LED_drawWarningLight);
      savePalette(LittleFS, "/LED_drawWarningLight.dat", targetConfig.LED_drawWarningLight, dataLen);
    }
  }
  if (LittleFS.exists("/LED_drawWarningSpeed.dat")) {
    targetConfig.LED_drawWarningLightSpeed = read_ul(LittleFS, "/LED_drawWarningLightSpeed.dat");
  } else {
    write_unsigned_long(LittleFS, "/LED_drawWarningLightSpeed.dat", targetConfig.LED_drawWarningLightSpeed);
  }
  if (LittleFS.exists("/LED_drawLight.dat")) {
    loadPalette(LittleFS, "/LED_drawLight.dat", (unsigned char*)targetConfig.LED_drawLight, sizeof(targetConfig.LED_drawLight));
  } else {
    size_t freeSpace = LittleFS.totalBytes() - LittleFS.usedBytes();
    if (freeSpace < 1024) {
      freeSpaceError = true;
    } else {
      size_t dataLen = strlen((const char*)targetConfig.LED_drawLight);
      savePalette(LittleFS, "/LED_drawLight.dat", targetConfig.LED_drawLight, dataLen);
    }
  }
  if (LittleFS.exists("/LED_drawLightSpeed.dat")) {
    targetConfig.LED_drawLightSpeed = read_ul(LittleFS, "/LED_drawLightSpeed.dat");
  } else {
    write_unsigned_long(LittleFS, "/LED_drawLightSpeed.dat", targetConfig.LED_drawLightSpeed);
  }
  if (LittleFS.exists("/LED_hit0s.dat")) {
    loadPalette(LittleFS, "/LED_hit0s.dat", (unsigned char*)targetConfig.LED_hit0s, sizeof(targetConfig.LED_hit0s));
  } else {
    size_t freeSpace = LittleFS.totalBytes() - LittleFS.usedBytes();
    if (freeSpace < 1024) {
      freeSpaceError = true;
    } else {
      size_t dataLen = strlen((const char*)targetConfig.LED_hit0s);
      savePalette(LittleFS, "/LED_hit0s.dat", targetConfig.LED_hit0s, dataLen);
    }
  }
  if (LittleFS.exists("/LED_hit0sSpeed.dat")) {
    targetConfig.LED_hit0sSpeed = read_ul(LittleFS, "/LED_hit0sSpeed.dat");
  } else {
    write_unsigned_long(LittleFS, "/LED_hit0sSpeed.dat", targetConfig.LED_hit0sSpeed);
  }
  if (LittleFS.exists("/LED_hit100s.dat")) {
    loadPalette(LittleFS, "/LED_hit100s.dat", (unsigned char*)targetConfig.LED_hit100s, sizeof(targetConfig.LED_hit100s));
  } else {
    size_t freeSpace = LittleFS.totalBytes() - LittleFS.usedBytes();
    if (freeSpace < 1024) {
      freeSpaceError = true;
    } else {
      size_t dataLen = strlen((const char*)targetConfig.LED_hit100s);
      savePalette(LittleFS, "/LED_hit100s.dat", targetConfig.LED_hit100s, dataLen);
    }
  }
  if (LittleFS.exists("/LED_hit100sSpeed.dat")) {
    targetConfig.LED_hit100sSpeed = read_ul(LittleFS, "/LED_hit100sSpeed.dat");
  } else {
    write_unsigned_long(LittleFS, "/LED_hit100sSpeed.dat", targetConfig.LED_hit100sSpeed);
  }
  if (LittleFS.exists("/LED_hit200s.dat")) {
    loadPalette(LittleFS, "/LED_hit200s.dat", (unsigned char*)targetConfig.LED_hit200s, sizeof(targetConfig.LED_hit200s));
  } else {
    size_t freeSpace = LittleFS.totalBytes() - LittleFS.usedBytes();
    if (freeSpace < 1024) {
      freeSpaceError = true;
    } else {
      size_t dataLen = strlen((const char*)targetConfig.LED_hit200s);
      savePalette(LittleFS, "/LED_hit200s.dat", targetConfig.LED_hit200s, dataLen);
    }
  }
  if (LittleFS.exists("/LED_hit200sSpeed.dat")) {
    targetConfig.LED_hit200sSpeed = read_ul(LittleFS, "/LED_hit200sSpeed.dat");
  } else {
    write_unsigned_long(LittleFS, "/LED_hit200sSpeed.dat", targetConfig.LED_hit200sSpeed);
  }
  if (LittleFS.exists("/LED_hit300s.dat")) {
    loadPalette(LittleFS, "/LED_hit300s.dat", (unsigned char*)targetConfig.LED_hit300s, sizeof(targetConfig.LED_hit300s));
  } else {
    size_t freeSpace = LittleFS.totalBytes() - LittleFS.usedBytes();
    if (freeSpace < 1024) {
      freeSpaceError = true;
    } else {
      size_t dataLen = strlen((const char*)targetConfig.LED_hit300s);
      savePalette(LittleFS, "/LED_hit300s.dat", targetConfig.LED_hit300s, dataLen);
    }
  }
  if (LittleFS.exists("/LED_hit300sSpeed.dat")) {
    targetConfig.LED_hit300sSpeed = read_ul(LittleFS, "/LED_hit300sSpeed.dat");
  } else {
    write_unsigned_long(LittleFS, "/LED_hit300sSpeed.dat", targetConfig.LED_hit300sSpeed);
  }
  if (LittleFS.exists("/LED_hit400s.dat")) {
    loadPalette(LittleFS, "/LED_hit400s.dat", (unsigned char*)targetConfig.LED_hit400s, sizeof(targetConfig.LED_hit400s));
  } else {
    size_t freeSpace = LittleFS.totalBytes() - LittleFS.usedBytes();
    if (freeSpace < 1024) {
      freeSpaceError = true;
    } else {
      size_t dataLen = strlen((const char*)targetConfig.LED_hit400s);
      savePalette(LittleFS, "/LED_hit400s.dat", targetConfig.LED_hit400s, dataLen);
    }
  }
  if (LittleFS.exists("/LED_hit400sSpeed.dat")) {
    targetConfig.LED_hit400sSpeed = read_ul(LittleFS, "/LED_hit400sSpeed.dat");
  } else {
    write_unsigned_long(LittleFS, "/LED_hit400sSpeed.dat", targetConfig.LED_hit400sSpeed);
  }
  if (LittleFS.exists("/LED_hit500s.dat")) {
    loadPalette(LittleFS, "/LED_hit500s.dat", (unsigned char*)targetConfig.LED_hit500s, sizeof(targetConfig.LED_hit500s));
  } else {
    size_t freeSpace = LittleFS.totalBytes() - LittleFS.usedBytes();
    if (freeSpace < 1024) {
      freeSpaceError = true;
    } else {
      size_t dataLen = strlen((const char*)targetConfig.LED_hit500s);
      savePalette(LittleFS, "/LED_hit500s.dat", targetConfig.LED_hit500s, dataLen);
    }
  }
  if (LittleFS.exists("/LED_hit500sSpeed.dat")) {
    targetConfig.LED_hit500sSpeed = read_ul(LittleFS, "/LED_hit500sSpeed.dat");
  } else {
    write_unsigned_long(LittleFS, "/LED_hit500sSpeed.dat", targetConfig.LED_hit500sSpeed);
  }
  if (LittleFS.exists("/LED_hit600s.dat")) {
    loadPalette(LittleFS, "/LED_hit600s.dat", (unsigned char*)targetConfig.LED_hit600s, sizeof(targetConfig.LED_hit600s));
  } else {
    size_t freeSpace = LittleFS.totalBytes() - LittleFS.usedBytes();
    if (freeSpace < 1024) {
      freeSpaceError = true;
    } else {
      size_t dataLen = strlen((const char*)targetConfig.LED_hit600s);
      savePalette(LittleFS, "/LED_hit600s.dat", targetConfig.LED_hit600s, dataLen);
    }
  }
  if (LittleFS.exists("/LED_hit600sSpeed.dat")) {
    targetConfig.LED_hit600sSpeed = read_ul(LittleFS, "/LED_hit600sSpeed.dat");
  } else {
    write_unsigned_long(LittleFS, "/LED_hit600sSpeed.dat", targetConfig.LED_hit600sSpeed);
  }
  if (LittleFS.exists("/LED_hit700s.dat")) {
    loadPalette(LittleFS, "/LED_hit700s.dat", (unsigned char*)targetConfig.LED_hit700s, sizeof(targetConfig.LED_hit700s));
  } else {
    size_t freeSpace = LittleFS.totalBytes() - LittleFS.usedBytes();
    if (freeSpace < 1024) {
      freeSpaceError = true;
    } else {
      size_t dataLen = strlen((const char*)targetConfig.LED_hit700s);
      savePalette(LittleFS, "/LED_hit700s.dat", targetConfig.LED_hit700s, dataLen);
    }
  }
  if (LittleFS.exists("/LED_hit700sSpeed.dat")) {
    targetConfig.LED_hit700sSpeed = read_ul(LittleFS, "/LED_hit700sSpeed.dat");
  } else {
    write_unsigned_long(LittleFS, "/LED_hit700sSpeed.dat", targetConfig.LED_hit700sSpeed);
  }
  if (LittleFS.exists("/LED_hit800s.dat")) {
    loadPalette(LittleFS, "/LED_hit800s.dat", (unsigned char*)targetConfig.LED_hit800s, sizeof(targetConfig.LED_hit800s));
  } else {
    size_t freeSpace = LittleFS.totalBytes() - LittleFS.usedBytes();
    if (freeSpace < 1024) {
      freeSpaceError = true;
    } else {
      size_t dataLen = strlen((const char*)targetConfig.LED_hit800s);
      savePalette(LittleFS, "/LED_hit800s.dat", targetConfig.LED_hit800s, dataLen);
    }
  }
  if (LittleFS.exists("/LED_hit800sSpeed.dat")) {
    targetConfig.LED_hit800sSpeed = read_ul(LittleFS, "/LED_hit800sSpeed.dat");
  } else {
    write_unsigned_long(LittleFS, "/LED_hit800sSpeed.dat", targetConfig.LED_hit800sSpeed);
  }
  if (LittleFS.exists("/LED_hit900s.dat")) {
    loadPalette(LittleFS, "/LED_hit900s.dat", (unsigned char*)targetConfig.LED_hit900s, sizeof(targetConfig.LED_hit900s));
  } else {
    size_t freeSpace = LittleFS.totalBytes() - LittleFS.usedBytes();
    if (freeSpace < 1024) {
      freeSpaceError = true;
    } else {
      size_t dataLen = strlen((const char*)targetConfig.LED_hit900s);
      savePalette(LittleFS, "/LED_hit900s.dat", targetConfig.LED_hit900s, dataLen);
    }
  }
  if (LittleFS.exists("/LED_hit900sSpeed.dat")) {
    targetConfig.LED_hit900sSpeed = read_ul(LittleFS, "/LED_hit900sSpeed.dat");
  } else {
    write_unsigned_long(LittleFS, "/LED_hit900sSpeed.dat", targetConfig.LED_hit900sSpeed);
  }
  if (LittleFS.exists("/LED_hit1000s.dat")) {
    loadPalette(LittleFS, "/LED_hit1000s.dat", (unsigned char*)targetConfig.LED_hit1000s, sizeof(targetConfig.LED_hit1000s));
  } else {
    size_t freeSpace = LittleFS.totalBytes() - LittleFS.usedBytes();
    if (freeSpace < 1024) {
      freeSpaceError = true;
    } else {
      size_t dataLen = strlen((const char*)targetConfig.LED_hit1000s);
      savePalette(LittleFS, "/LED_hit1000s.dat", targetConfig.LED_hit1000s, dataLen);
    }
  }
  if (LittleFS.exists("/LED_hit1000sSpeed.dat")) {
    targetConfig.LED_hit1000sSpeed = read_ul(LittleFS, "/LED_hit1000sSpeed.dat");
  } else {
    write_unsigned_long(LittleFS, "/LED_hit1000sSpeed.dat", targetConfig.LED_hit1000sSpeed);
  }
  if (LittleFS.exists("/LED_hit1100s.dat")) {
    loadPalette(LittleFS, "/LED_hit1100s.dat", (unsigned char*)targetConfig.LED_hit1100s, sizeof(targetConfig.LED_hit1100s));
  } else {
    size_t freeSpace = LittleFS.totalBytes() - LittleFS.usedBytes();
    if (freeSpace < 1024) {
      freeSpaceError = true;
    } else {
      size_t dataLen = strlen((const char*)targetConfig.LED_hit1100s);
      savePalette(LittleFS, "/LED_hit1100s.dat", targetConfig.LED_hit1100s, dataLen);
    }
  }
  if (LittleFS.exists("/LED_hit1100sSpeed.dat")) {
    targetConfig.LED_hit1100sSpeed = read_ul(LittleFS, "/LED_hit1100sSpeed.dat");
  } else {
    write_unsigned_long(LittleFS, "/LED_hit1100sSpeed.dat", targetConfig.LED_hit1100sSpeed);
  }
  if (LittleFS.exists("/LED_hit1200s.dat")) {
    loadPalette(LittleFS, "/LED_hit1200s.dat", (unsigned char*)targetConfig.LED_hit1200s, sizeof(targetConfig.LED_hit1200s));
  } else {
    size_t freeSpace = LittleFS.totalBytes() - LittleFS.usedBytes();
    if (freeSpace < 1024) {
      freeSpaceError = true;
    } else {
      size_t dataLen = strlen((const char*)targetConfig.LED_hit1200s);
      savePalette(LittleFS, "/LED_hit1200s.dat", targetConfig.LED_hit1200s, dataLen);
    }
  }
  if (LittleFS.exists("/LED_hit1200sSpeed.dat")) {
    targetConfig.LED_hit1200sSpeed = read_ul(LittleFS, "/LED_hit1200sSpeed.dat");
  } else {
    write_unsigned_long(LittleFS, "/LED_hit1200sSpeed.dat", targetConfig.LED_hit1200sSpeed);
  }
  if (LittleFS.exists("/LED_hit1300s.dat")) {
    loadPalette(LittleFS, "/LED_hit1300s.dat", (unsigned char*)targetConfig.LED_hit1300s, sizeof(targetConfig.LED_hit1300s));
  } else {
    size_t freeSpace = LittleFS.totalBytes() - LittleFS.usedBytes();
    if (freeSpace < 1024) {
      freeSpaceError = true;
    } else {
      size_t dataLen = strlen((const char*)targetConfig.LED_hit1300s);
      savePalette(LittleFS, "/LED_hit1300s.dat", targetConfig.LED_hit1300s, dataLen);
    }
  }
  if (LittleFS.exists("/LED_hit1300sSpeed.dat")) {
    targetConfig.LED_hit1300sSpeed = read_ul(LittleFS, "/LED_hit1300sSpeed.dat");
  } else {
    write_unsigned_long(LittleFS, "/LED_hit1300sSpeed.dat", targetConfig.LED_hit1300sSpeed);
  }
  if (LittleFS.exists("/LED_hit1400s.dat")) {
    loadPalette(LittleFS, "/LED_hit1400s.dat", (unsigned char*)targetConfig.LED_hit1400s, sizeof(targetConfig.LED_hit1400s));
  } else {
    size_t freeSpace = LittleFS.totalBytes() - LittleFS.usedBytes();
    if (freeSpace < 1024) {
      freeSpaceError = true;
    } else {
      size_t dataLen = strlen((const char*)targetConfig.LED_hit1400s);
      savePalette(LittleFS, "/LED_hit1400s.dat", targetConfig.LED_hit1400s, dataLen);
    }
  }
  if (LittleFS.exists("/LED_hit1400sSpeed.dat")) {
    targetConfig.LED_hit1400sSpeed = read_ul(LittleFS, "/LED_hit1400sSpeed.dat");
  } else {
    write_unsigned_long(LittleFS, "/LED_hit1400sSpeed.dat", targetConfig.LED_hit1400sSpeed);
  }
  if (LittleFS.exists("/LED_hit1500plus.dat")) {
    loadPalette(LittleFS, "/LED_hit1500plus.dat", (unsigned char*)targetConfig.LED_hit1500plus, sizeof(targetConfig.LED_hit1500plus));
  } else {
    size_t freeSpace = LittleFS.totalBytes() - LittleFS.usedBytes();
    if (freeSpace < 1024) {
      freeSpaceError = true;
    } else {
      size_t dataLen = strlen((const char*)targetConfig.LED_hit1500plus);
      savePalette(LittleFS, "/LED_hit1500plus.dat", targetConfig.LED_hit1500plus, dataLen);
    }
  }
  if (LittleFS.exists("/LED_hit1500plusSpeed.dat")) {
    targetConfig.LED_hit1500plusSpeed = read_ul(LittleFS, "/LED_hit1500plusSpeed.dat");
  } else {
    write_unsigned_long(LittleFS, "/LED_hit1500plusSpeed.dat", targetConfig.LED_hit1500plusSpeed);
  }
  //--- end load saved data ---//

  //--- LED setup ---//
  FastLED.addLeds<LED_TYPE, LED_PIN, COLOR_ORDER>(leds, NUM_LEDS).setCorrection(TypicalLEDStrip);
  //FastLED.addLeds<LED_TYPE, LED_PIN, COLOR_ORDER>(leds, NUM_LEDS);
  FastLED.setCorrection(TypicalLEDStrip);
  FastLED.setBrightness(targetConfig.BRIGHTNESS);
  FastLED.setDither(BINARY_DITHER);
  FastLED.clear();  // clear possible stuck light
  delay(10);
  FastLED.show();
  //--- end LED setup ---//

  //--- WiFi setup ---//
  Serial.println("***** Starting WiFi");

  if (targetConfig.homeNetworkToggle) {
    WiFi.mode(WIFI_AP_STA);
    Serial.printf("Connecting to: %s\n", targetConfig.HOME_SSID);
    WiFi.begin(targetConfig.HOME_SSID, targetConfig.HOME_PASS);

    int attempts = 0;
    // Attempt to connect 5 times (5 seconds)
    while (WiFi.status() != WL_CONNECTED && attempts < 10) {
      delay(1000);
      attempts++;
      Serial.printf("Attempt %d/10: Setting as a Wi-Fi Station..\n", attempts);
    }

    if (WiFi.status() == WL_CONNECTED) {
      Serial.print("Station IP Address: ");
      Serial.println(WiFi.localIP());
      Serial.print("Wi-Fi Channel: ");
      Serial.println(WiFi.channel());
    } else {
      Serial.println("***** Connection failed! Falling back to AP Mode...");
    }
  }

  // Check if we are NOT connected (either by choice or fallback)
  if (WiFi.status() != WL_CONNECTED) {
    WiFi.mode(WIFI_AP);  // Ensure we aren't still trying to be a Station
    Serial.print("Setting AP (Access Point): ");
    Serial.println(targetConfig.OPEN_SSID);

    WiFi.softAP(targetConfig.OPEN_SSID);
    IPAddress IP = WiFi.softAPIP();
    Serial.print("AP IP address: ");
    Serial.println(IP);
    FLAG_AP_mode = true;
  }
  //--- end Wifi setup ---//

  //--- begin mDNS ---//
  if (!MDNS.begin(targetConfig.dns_name)) {
    Serial.println("Error setting up MDNS responder!");
    while (1) {
      delay(1000);
    }
  }
  Serial.print("mDNS responder started: ");
  Serial.println(targetConfig.dns_name);

  //--- Webserver work ---//
  //--- index.html
  server.on("/", HTTP_GET, [](AsyncWebServerRequest* request) {
    request->send(200, "text/html", index_html);
    Serial.println("**************************************** index.html served");
  });
  //--- settings.html
  server.on("/settings", HTTP_GET, [](AsyncWebServerRequest* request) {
    request->send(200, "text/html", settings_html, processor);
    Serial.println("**************************************** settings.html served");
  });

  ws.onEvent(onEvent);  // Connects the handler
  server.addHandler(&ws);
  server.begin();
  //--- end Webserver setup ---//

  //--- Check for updates ---//
  checkForUpdates();

  if (targetConfig.startupLightToggle) {
    FLAG_showStartupLight = true;
  }

  Serial.print("targetConfig.startupLightToggle: ");
  Serial.println(targetConfig.startupLightToggle);
  Serial.print("targetConfig.LED_startupLight: ");
  Serial.println((char*)targetConfig.LED_startupLight);
  Serial.print("targetConfig.LED_startupLightSpeed: ");
  Serial.println(targetConfig.LED_startupLightSpeed);

  Serial.println("================== setup() complete, ready to shoot ====================");
}  // end setup()

void loop() {
  currentMillis = millis();
  ws.cleanupClients();  // websocket cleanup. do not remove.

  if (startUpdateNow) {
    startUpdateNow = false; // Reset flag immediately
    Serial.println("Starting Stable OTA from Loop...");

    // Disable Watchdog for Core 3.x
    #include "esp_task_wdt.h"
    esp_task_wdt_config_t twdt_config = { .timeout_ms = 300000, .trigger_panic = true };
    esp_task_wdt_reconfigure(&twdt_config);

    WiFiClientSecure otaClient;
    otaClient.setInsecure();
    httpUpdate.setFollowRedirects(HTTPC_STRICT_FOLLOW_REDIRECTS);
    httpUpdate.onProgress(update_progress);
    
    // The actual update
    httpUpdate.update(otaClient, newBinUrl);
  }

  // 1. Auto-Draw Logic
  if (targetConfig.targetAutoDrawToggle && !targetAutoDraw_hold && (currentMillis - targetAutoDrawMillis >= (targetConfig.AUTODRAW_SECS * 1000))) {
    targetAutoDraw_hold = true; // change opposite day flag
    set_target(); // virtually press the Draw button
  }

  // 2. Auto-Reset Logic
  if (resetState && targetConfig.autoResetToggle && (currentMillis - autoResetMillis >= (targetConfig.RESET_SECS * 1000))) {
    reset_target();
  }

  // 3. Target State Machine
  if (targetActiveState) {
    if (targetWarmUpState) {
      adxl.getInterruptSource();  // Dummy read
      targetWarmUpState = false;
      return;  // nope out here so we don't immediately check the timer on the next line.
    }

    if (FLAG_drawWarning && currentMillis - countdownMillis >= drawWarningMillis) {
      !FLAG_drawWarning;
      if (targetConfig.drawWarningSoundToggle) {
        ws.textAll("playTone : true");
      }
      if (targetConfig.drawWarningLightToggle) {
        // TODO: trigger warning light (200ms on, 200ms off for 3 flashes totaling 1 second)
      }
    }

    if (currentMillis - countdownMillis >= drawMillis) {
      if (startDraw) {
        Serial.println("--- DRAW! ---");
        drawFlashState = true;  // enable draw flash
        timerMicros = micros();
        startDraw = false;  // only do this block of code once
        if (targetConfig.autoResetToggle) autoResetMillis = millis();
        return;  // nope out here. No reason to look for hit on next beat.
      }

      byte interrupts = adxl.getInterruptSource();
      if (adxl.triggered(interrupts, ADXL345_SINGLE_TAP)) {
        shotTime_micros = micros() - timerMicros;
        targetActiveState = drawFlashState = false;
        hitFlashState = true;
        settle_target_hit();
        broadcastStats();
      } else if (micros() - timerMicros >= (targetConfig.TARGET_TIMEOUT * 1000000)) {
        drawFlashState = targetActiveState = false;
        shotTime_micros = 0;
        if (testState) {
          testState = false;
          strncpy(allButLast3, test_exp, sizeof(allButLast3) - 1);
        } else {
          settle_target_miss();
        }
        broadcastStats();
      }
    }
  }

  if (hitFlashState) {
    uint32_t t = shotTime_micros;
    if (t < 300000) processHitVisuals(targetConfig.LED_hit200s, targetConfig.LED_hit200sSpeed);
    else if (t < 400000) processHitVisuals(targetConfig.LED_hit300s, targetConfig.LED_hit300sSpeed);
    else if (t < 500000) processHitVisuals(targetConfig.LED_hit400s, targetConfig.LED_hit400sSpeed);
    else if (t < 600000) processHitVisuals(targetConfig.LED_hit500s, targetConfig.LED_hit500sSpeed);
    else if (t < 700000) processHitVisuals(targetConfig.LED_hit600s, targetConfig.LED_hit600sSpeed);
    else if (t < 800000) processHitVisuals(targetConfig.LED_hit700s, targetConfig.LED_hit700sSpeed);
    else if (t < 900000) processHitVisuals(targetConfig.LED_hit800s, targetConfig.LED_hit800sSpeed);
    else if (t < 1000000) processHitVisuals(targetConfig.LED_hit900s, targetConfig.LED_hit900sSpeed);
    else if (t < 1100000) processHitVisuals(targetConfig.LED_hit1000s, targetConfig.LED_hit1000sSpeed);
    else if (t < 1200000) processHitVisuals(targetConfig.LED_hit1100s, targetConfig.LED_hit1100sSpeed);
    else processHitVisuals(targetConfig.LED_hit1200s, targetConfig.LED_hit1200sSpeed);
  } else if (drawFlashState) {
    uint8_t currentScaledMax = map(targetConfig.BRIGHTNESS, 0, 100, 0, 255);
    if (strstr(targetConfig.LED_drawLight, "Colors_p") != NULL) {
      static uint8_t startIndex = 0;
      static unsigned long lastDrawUpdate = 0;
      if (millis() - lastDrawUpdate > 33) {
        startIndex += targetConfig.LED_drawLightSpeed;
        lastDrawUpdate = millis();
      }
      FillLEDsFromPaletteColors(getPaletteFromName(targetConfig.LED_drawLight), startIndex, currentScaledMax);
    } else {
      CRGB color = getCRGBFromName(targetConfig.LED_drawLight);
      CHSV hsvColor = rgb2hsv_approximate(color);
      uint8_t currentPulseVal = (targetConfig.LED_drawLightSpeed == 0) ? currentScaledMax : beatsin8(map(targetConfig.LED_drawLightSpeed, 1, 10, 60, 500), 0, currentScaledMax, 0, 64);
      fill_solid(leds, NUM_LEDS, CHSV(hsvColor.hue, hsvColor.sat, currentPulseVal));
    }
    FastLED.show();
  } else if (FLAG_toggleLight) {
    uint8_t toggleScaledMax = map(targetConfig.BRIGHTNESS, 0, 100, 0, 255);
    if (strstr(targetConfig.LED_drawLight, "Colors_p") != NULL) {
      static uint8_t toggleStartIndex = 0;
      static unsigned long lastToggleUpdate = 0;
      if (millis() - lastToggleUpdate > 33) {
        toggleStartIndex += targetConfig.LED_drawLightSpeed;
        lastToggleUpdate = millis();
      }
      FillLEDsFromPaletteColors(getPaletteFromName(targetConfig.LED_drawLight), toggleStartIndex, toggleScaledMax);
    } else {
      CRGB color = getCRGBFromName(targetConfig.LED_drawLight);
      CHSV hsvColor = rgb2hsv_approximate(color);
      uint8_t togglePulseVal = (targetConfig.LED_drawLightSpeed == 0) ? toggleScaledMax : beatsin8(map(targetConfig.LED_drawLightSpeed, 1, 10, 60, 500), 0, toggleScaledMax, 0, 64);
      fill_solid(leds, NUM_LEDS, CHSV(hsvColor.hue, hsvColor.sat, togglePulseVal));
    }
    FastLED.show();
  } else if (FLAG_showStartupLight) {
    uint8_t startupScaledMax = map(targetConfig.BRIGHTNESS, 0, 100, 0, 255);
    if (strstr(targetConfig.LED_startupLight, "Colors_p") != NULL) {
      static uint8_t startupStartIndex = 0;
      static unsigned long lastStartupUpdate = 0;
      if (millis() - lastStartupUpdate > 33) {
        startupStartIndex += targetConfig.LED_startupLightSpeed;
        lastStartupUpdate = millis();
      }
      FillLEDsFromPaletteColors(getPaletteFromName(targetConfig.LED_startupLight), startupStartIndex, startupScaledMax);
    } else {
      CRGB color = getCRGBFromName(targetConfig.LED_startupLight);
      CHSV hsvColor = rgb2hsv_approximate(color);
      uint8_t startupPulseVal = (targetConfig.LED_startupLightSpeed == 0) ? startupScaledMax : beatsin8(map(targetConfig.LED_startupLightSpeed, 1, 10, 60, 500), 0, startupScaledMax, 0, 64);
      fill_solid(leds, NUM_LEDS, CHSV(hsvColor.hue, hsvColor.sat, startupPulseVal));
    }
    FastLED.show();
  }

  // 5. Hobbs Meter (No changes needed)
  if (currentMillis - hobbsMeterMillis >= 360000 && !startDraw && !targetActiveState && !hitFlashState && !drawFlashState) {
    hobbsMeter++;
    write_unsigned_long(LittleFS, "/hobbsMeter.dat", hobbsMeter);
    hobbsMeterMillis = currentMillis;
  }
}
