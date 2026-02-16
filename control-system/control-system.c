// control-system.c
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>
#include <string.h>

#include "pico/stdlib.h"
#include "hardware/gpio.h"
#include "hardware/flash.h"
#include "hardware/sync.h"
#include "pico/unique_id.h"

#include "port_common.h"

#include "wizchip_conf.h"
#include "wizchip_spi.h"

#include "dhcp.h"
#include "dns.h"
#include "timer.h"

#include "socket.h"
#include "ping.h"

#include "httpServer.h"
#include "web_page.h"

/* Buffer */
#define ETHERNET_BUF_MAX_SIZE (1024 * 2)

/* Sockets */
#define SOCKET_DHCP 0
#define SOCKET_DNS  1

/* ICMP Ping socket (keep away from DHCP/DNS/HTTP) */
#define SOCKET_PING 4

/* Connectivity monitoring parameters */
#define PHY_POLL_MS          500
#define PING_INTERVAL_MS     10000  // Increased from 5000 to 10 seconds - less aggressive
#define PING_TIMEOUT_MS      2000   // Increased from 800 to 2000ms - more lenient timeout
#define PING_FAIL_THRESHOLD  3      // Need 3 consecutive failures before marking as offline
#define OFFLINE_SHUTDOWN_DELAY_MS  10000  // Delay before shutting down relays when offline (10 seconds)

/* Put HTTP on different sockets than DHCP/DNS */
#define HTTP_SOCKET_MAX_NUM 2
static uint8_t g_http_socket_num_list[HTTP_SOCKET_MAX_NUM] = {2, 3};

/* Network
 * NOTE: Must be global because ping.c expects: `extern wiz_NetInfo net_info;`
 */
wiz_NetInfo net_info = {
    .mac = {0x00, 0x08, 0xDC, 0x12, 0x34, 0x56},
    .ip  = {0, 0, 0, 0},
    .sn  = {0, 0, 0, 0},
    .gw  = {0, 0, 0, 0},
    .dns = {0, 0, 0, 0},
#if _WIZCHIP_ > W5500
    /* Keep the same pattern as other W6100 examples */
    .lla = {
        0xfe, 0x80, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00,
        0x02, 0x08, 0xdc, 0xff,
        0xfe, 0x57, 0x57, 0x25
    },
    .gua = {
        0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00
    },
    .sn6 = {
        0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff,
        0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00
    },
    .gw6 = {
        0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00
    },
    .dns6 = {
        0x20, 0x01, 0x48, 0x60,
        0x48, 0x60, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x88, 0x88
    },
    .dhcp = NETINFO_DHCP,
    .ipmode = NETINFO_STATIC_ALL
#else
    .dhcp = NETINFO_DHCP
#endif
};

/* ping.c also references this symbol for IPv6 paths (even if you only use IPv4). */
uint8_t remote_ip6[16] = {0};

/* Common buffer (DHCP/DNS need this) */
static uint8_t g_ethernet_buf[ETHERNET_BUF_MAX_SIZE] = {0};

/* HTTP buffers */
static uint8_t g_http_send_buf[ETHERNET_BUF_MAX_SIZE] = {0};
static uint8_t g_http_recv_buf[ETHERNET_BUF_MAX_SIZE] = {0};

/* Flags */
static uint8_t g_dhcp_get_ip_flag = 0;
static uint8_t g_http_started = 0;

/* Track “network ever worked” */
static bool g_has_ever_leased = false;

/* Timer */
static volatile uint16_t g_msec_cnt = 0;

/* DHCP callbacks */
static void wizchip_dhcp_assign(void);
static void wizchip_dhcp_conflict(void);

static void set_unique_mac(wiz_NetInfo *net)
{
    pico_unique_board_id_t id;
    pico_get_unique_board_id(&id);

    // Locally administered MAC: 02:xx:xx:xx:xx:xx
    net->mac[0] = 0x02;
    net->mac[1] = id.id[0];
    net->mac[2] = id.id[1];
    net->mac[3] = id.id[2];
    net->mac[4] = id.id[3];
    net->mac[5] = id.id[4];
}

/* ===== Relay control (GP6..GP9) ===== */
#define RELAY1_PIN 6
#define RELAY2_PIN 7
#define RELAY3_PIN 8
#define RELAY4_PIN 9

/* If your relay board is active-low, set to 0 (and OFF becomes 1). */
#define RELAY_ACTIVE_LEVEL 1

static const uint8_t g_relay_pins[4] = { RELAY1_PIN, RELAY2_PIN, RELAY3_PIN, RELAY4_PIN };
static bool g_relay_state[4] = { false, false, false, false }; // false=OFF, true=ON

// Saved relay states before shutdown (for restore on network recovery)
static bool g_relay_state_saved[4] = { false, false, false, false };
static bool g_relay_state_has_saved = false;  // Track if we have saved states to restore

/* Flash storage for relay states */
#define RELAY_STATE_MAGIC    0x524C4159  // "RELA" in ASCII
#define RELAY_STATE_VERSION  1
#define RELAY_STATE_FLASH_OFFSET  (PICO_FLASH_SIZE_BYTES - FLASH_SECTOR_SIZE)  // Last sector

typedef struct {
    uint32_t magic;      // Magic number to validate data
    uint32_t version;    // Version for future compatibility
    bool relay_state[4]; // Relay states
    uint32_t checksum;   // Simple checksum (sum of all bytes)
} relay_state_flash_t;

static absolute_time_t g_last_flash_save_time = 0;
#define FLASH_SAVE_DEBOUNCE_MS  2000  // Don't save more than once per 2 seconds

/* Forward declarations */
static void relay_all_apply(bool on);
static void relay_apply(int idx, bool on);

/* ===== External LEDs (5x) + switch =====
 * IMPORTANT: If any of these GPIOs overlap with your W6100 wiring on your specific board,
 * just change these defines. Logic stays the same.
 */
#define EXT_LED1_PIN 10  // Status LED
#define EXT_LED2_PIN 11  // Relay1 indicator
#define EXT_LED3_PIN 12  // Relay2 indicator
#define EXT_LED4_PIN 13  // Relay3 indicator
#define EXT_LED5_PIN 14  // Relay4 indicator

#define EXT_LED_ACTIVE_LEVEL 1

#define SWITCH_PIN 15
#define SWITCH_ACTIVE_LOW 1  // internal pull-up; ON when pin reads 0

#define RESET_BUTTON_PIN 5
#define RESET_BUTTON_HOLD_TIME_MS  1000  // Must hold for 1 second to reset

static const uint8_t g_ext_led_pins[5] = { EXT_LED1_PIN, EXT_LED2_PIN, EXT_LED3_PIN, EXT_LED4_PIN, EXT_LED5_PIN };

/* LED1 (status) runtime state machine */
typedef enum {
    NET_STATE_BOOT = 0,
    NET_STATE_WAIT_DHCP,
    NET_STATE_ONLINE,
    NET_STATE_OFFLINE,  // link is down OR gateway is not reachable
    NET_STATE_LOST
} net_state_t;

static net_state_t g_net_state = NET_STATE_BOOT;
static bool g_led1_level = false;
static absolute_time_t g_led1_next_toggle;

/* Physical link + upstream reachability monitoring */
static bool g_phy_link_up = true;
static absolute_time_t g_next_phy_poll;

typedef enum { PING_ST_IDLE = 0, PING_ST_WAIT } ping_state_t;
typedef enum { PING_FAIL_NONE = 0, PING_FAIL_SOCKET, PING_FAIL_SEND, PING_FAIL_TIMEOUT, PING_FAIL_WRONG_REPLY } ping_fail_reason_t;

static struct {
    bool enabled;
    bool l3_ok;
    int fail_streak;
    ping_state_t st;
    absolute_time_t next_due;
    absolute_time_t deadline;
    uint16_t expected_id;      // ICMP ID we're waiting for
    uint16_t expected_seqnum;  // ICMP sequence number we're waiting for
    ping_fail_reason_t last_fail_reason;  // Reason for last failure
    uint8_t socket_state;      // Current socket state (for diagnostics)
    int32_t rx_bytes_waiting;  // Bytes waiting in RX buffer (for diagnostics)
    int send_attempts;         // Number of ping requests sent
    int reply_attempts;         // Number of reply checks performed
    uint8_t last_received_ip[4];  // IP of last received packet
    uint8_t last_received_type;   // First byte of last received packet (ICMP type)
    int32_t last_received_len;    // Length of last received packet
} g_ping = {
    .enabled = false,
    .l3_ok = true,
    .fail_streak = 0,
    .st = PING_ST_IDLE,
    .expected_id = 0,
    .expected_seqnum = 0,
    .last_fail_reason = PING_FAIL_NONE,
    .socket_state = 0,
    .rx_bytes_waiting = 0,
    .send_attempts = 0,
    .reply_attempts = 0,
    .last_received_ip = {0, 0, 0, 0},
    .last_received_type = 0,
    .last_received_len = 0,
};

static bool g_offline = false;
static absolute_time_t g_offline_start_time = 0;  // Timestamp when offline state started

/* --- External LED helpers --- */
static inline void ext_led_set_idx(int idx0, bool on)
{
    if (idx0 < 0 || idx0 > 4) return;
    const bool level = on ? (EXT_LED_ACTIVE_LEVEL ? 1 : 0)
                          : (EXT_LED_ACTIVE_LEVEL ? 0 : 1);
    gpio_put(g_ext_led_pins[idx0], level);
}

static void ext_leds_init(void)
{
    for (int i = 0; i < 5; i++)
    {
        gpio_init(g_ext_led_pins[i]);
        gpio_set_dir(g_ext_led_pins[i], GPIO_OUT);
        ext_led_set_idx(i, false);
    }
}

/* boot animation: LED1..LED5 blink in sequence, 0.5s each */
static void ext_led_boot_sequence(void)
{
    for (int i = 0; i < 5; i++)
    {
        ext_led_set_idx(i, true);
        sleep_ms(500);
        ext_led_set_idx(i, false);
    }
}

/* Relay -> LED2..LED5 mapping (relay1->LED2, relay2->LED3, ...) */
static void ext_led_update_relay_indicator(int relay_idx, bool relay_on)
{
    // relay_idx 0..3 maps to led_idx 1..4
    const int led_idx = relay_idx + 1;
    ext_led_set_idx(led_idx, relay_on);
}

static void ext_led_sync_relays(void)
{
    for (int i = 0; i < 4; i++)
        ext_led_update_relay_indicator(i, g_relay_state[i]);
}

/* Switch input */
static void switch_init(void)
{
    gpio_init(SWITCH_PIN);
    gpio_set_dir(SWITCH_PIN, GPIO_IN);
    gpio_pull_up(SWITCH_PIN);
}

static inline bool switch_is_on(void)
{
    const bool raw = gpio_get(SWITCH_PIN) ? true : false;
#if SWITCH_ACTIVE_LOW
    return raw ? false : true; // raw=0 => ON
#else
    return raw ? true : false;
#endif
}

/* Reset button (GPIO 5) - held for 1 second resets all relays to OFF */
static absolute_time_t g_reset_button_press_start = 0;
static bool g_reset_button_was_pressed = false;
static bool g_reset_button_triggered = false;  // Prevent repeated triggers while held

static void reset_button_init(void)
{
    gpio_init(RESET_BUTTON_PIN);
    gpio_set_dir(RESET_BUTTON_PIN, GPIO_IN);
    gpio_pull_up(RESET_BUTTON_PIN);  // Pull high, button press pulls low
}

static bool reset_button_is_pressed(void)
{
    // Button is pressed when pin reads LOW (pulled down)
    return gpio_get(RESET_BUTTON_PIN) == 0;
}

static void reset_button_tick(void)
{
    const absolute_time_t now = get_absolute_time();
    bool pressed = reset_button_is_pressed();
    
    if (pressed)
    {
        if (!g_reset_button_was_pressed)
        {
            // Button just pressed - record start time
            g_reset_button_press_start = now;
            g_reset_button_was_pressed = true;
            g_reset_button_triggered = false;  // Reset trigger flag on new press
        }
        else if (!g_reset_button_triggered)
        {
            // Button still pressed - check if held long enough
            int64_t hold_duration_ms = absolute_time_diff_us(g_reset_button_press_start, now) / 1000;
            
            if (hold_duration_ms >= RESET_BUTTON_HOLD_TIME_MS)
            {
                // Button held for >= 1 second - reset all relays
                printf("[RESET] Reset button held for %lld ms - resetting all relays to OFF\n", hold_duration_ms);
                
                // Turn off all relays immediately
                relay_all_apply(false);
                
                // Reset flash storage (erase the sector to clear saved states)
                uint32_t ints = save_and_disable_interrupts();
                flash_range_erase(RELAY_STATE_FLASH_OFFSET, FLASH_SECTOR_SIZE);
                restore_interrupts(ints);
                
                printf("[RESET] All relays reset to OFF and flash memory cleared\n");
                
                // Mark as triggered to prevent repeated actions while button is still held
                g_reset_button_triggered = true;
            }
        }
    }
    else
    {
        // Button released - reset tracking
        g_reset_button_was_pressed = false;
        g_reset_button_press_start = 0;
        g_reset_button_triggered = false;
    }
}

/* Status LED (external LED1) logic:
 * - Fast blink until DHCP success
 * - Solid ON when online
 * - Slow blink if connectivity is lost after having been online
 */
static void status_led1_set_mode(net_state_t st)
{
    g_net_state = st;

    if (st == NET_STATE_ONLINE)
    {
        g_led1_level = true;
        ext_led_set_idx(0, true);
        return;
    }

    // Blink modes
    g_led1_level = false;
    ext_led_set_idx(0, false);

    // schedule immediate toggle so it starts blinking promptly
    g_led1_next_toggle = make_timeout_time_ms(1);
}

static void status_led1_update(void)
{
    uint32_t period_ms = 0;

    switch (g_net_state)
    {
        case NET_STATE_WAIT_DHCP: period_ms = 150; break;  // fast blink
        case NET_STATE_OFFLINE:   period_ms = 1400; break; // very slow blink (cable unplugged / no upstream)
        case NET_STATE_LOST:      period_ms = 900; break;  // slow blink
        default: return; // BOOT or ONLINE handled elsewhere
    }

    if (absolute_time_diff_us(get_absolute_time(), g_led1_next_toggle) <= 0)
    {
        g_led1_level = !g_led1_level;
        ext_led_set_idx(0, g_led1_level);
        g_led1_next_toggle = make_timeout_time_ms(period_ms);
    }
}

/* ===== Connectivity monitoring (PHY link + ICMP ping to gateway) ===== */

// Protocol number for ICMP in IPRAW mode
#define IPPROTO_ICMP 1

#if   (_WIZCHIP_ == W5100S)
#define PING_Sn_PROTO(sn)   (_W5100S_IO_BASE_ + WIZCHIP_SREG_BLOCK(sn) + (0x0014))
#elif (_WIZCHIP_ == W5500)
#define PING_Sn_PROTO(N)    (_W5500_IO_BASE_ + (0x0014 << 8) + (WIZCHIP_SREG_BLOCK(N) << 3))
#elif (_WIZCHIP_ == W6100)
#define PING_Sn_PROTO(N)    _Sn_PNR_(N)
#elif (_WIZCHIP_ == W6300)
#define PING_Sn_PROTO(N)    _Sn_PNR_(N)
#endif

static inline bool gw_configured(void)
{
    return (net_info.gw[0] | net_info.gw[1] | net_info.gw[2] | net_info.gw[3]) != 0;
}

static void ping_monitor_reset(void)
{
    g_ping.st = PING_ST_IDLE;
    g_ping.fail_streak = 0;
    g_ping.l3_ok = true;   // neutral until we start checking
    g_ping.expected_id = 0;
    g_ping.expected_seqnum = 0;
    g_ping.last_fail_reason = PING_FAIL_NONE;
    g_ping.socket_state = 0;
    g_ping.rx_bytes_waiting = 0;

    // Best-effort close; harmless if already closed
    close(SOCKET_PING);
}

static void ping_socket_ensure_open(void)
{
    uint8_t sr = getSn_SR(SOCKET_PING);
    if (sr == SOCK_IPRAW)
        return;

    close(SOCKET_PING);

    // For IPRAW, proto must be set before socket() on WIZnet ioLibrary.
    WIZCHIP_WRITE(PING_Sn_PROTO(SOCKET_PING), IPPROTO_ICMP);

    // Local port is used as ICMP identifier; keep it stable
    // Note: IPRAW sockets on W6100 don't support SF_IO_NONBLOCK flag,
    // but recvfrom should be safe if we check getSn_RX_RSR first
    (void)socket(SOCKET_PING, Sn_MR_IPRAW, 3000, 0);
}

static bool ping_consume_reply_from(uint8_t sn, const uint8_t expect_ip[4])
{
    // Verify socket is in correct state before attempting to receive
    uint8_t sr = getSn_SR(sn);
    if (sr != SOCK_IPRAW)
        return false;

    int32_t rlen = getSn_RX_RSR(sn);
    if (rlen <= 0)
        return false;

    if (rlen > 255)
        rlen = 255;

    uint8_t addr[4];
    uint16_t port = 0;
    uint8_t buf[256] = {0};
    uint8_t addrlen = 4;  // IPv4 address length for W6100

    // Store expected bytes before recvfrom
    g_ping.last_received_len = rlen;
    
    // For W6100, explicitly call recvfrom_W6x00 to ensure correct function is used
    // Note: When IPV6_AVAILABLE is defined, the library checks if *addr == 0 and returns SOCKERR_ARG
    // So we initialize addr to non-zero values (though it will be overwritten by recvfrom)
    addr[0] = 0xFF;
    addr[1] = 0xFF;
    addr[2] = 0xFF;
    addr[3] = 0xFF;
    
    int32_t len = recvfrom_W6x00(sn, buf, (uint16_t)rlen, addr, &port, &addrlen);
    
    // Store diagnostic info about what we received (even if recvfrom failed)
    memcpy(g_ping.last_received_ip, addr, 4);
    if (len > 0)
    {
        g_ping.last_received_type = buf[0];
        g_ping.last_received_len = len;  // Actual bytes received
    }
    else
    {
        // recvfrom failed - use special marker
        // Note: SOCK_BUSY = 0, so len=0 could mean busy or actual failure
        g_ping.last_received_type = 255;  // Special marker for recvfrom failure
        g_ping.last_received_len = len;   // Error code (0 or negative)
    }
    
    if (len <= 0)
        return false;

    // ICMP echo reply has Type=0 at byte 0 in this library’s wire format
    if (buf[0] != 0)
    {
        // Not an echo reply - update failure reason
        g_ping.last_fail_reason = PING_FAIL_WRONG_REPLY;
        return false;
    }

    if (memcmp(addr, expect_ip, 4) != 0)
    {
        // Reply from wrong IP - update failure reason
        g_ping.last_fail_reason = PING_FAIL_WRONG_REPLY;
        return false;
    }

    return true;
}

static void connectivity_monitors_tick(bool dhcp_leased, bool switch_on)
{
    const absolute_time_t now = get_absolute_time();

    // --- PHY link polling (non-blocking, periodic)
    if (absolute_time_diff_us(now, g_next_phy_poll) <= 0)
    {
        int8_t link = wizphy_getphylink();
        g_phy_link_up = (link == PHY_LINK_ON);
        g_next_phy_poll = make_timeout_time_ms(PHY_POLL_MS);

        // If the link drops, reset ping machinery aggressively.
        if (!g_phy_link_up)
            ping_monitor_reset();
    }

    // --- ICMP ping to gateway (only meaningful after DHCP lease & link up)
    if (g_phy_link_up && dhcp_leased && gw_configured())
    {
        if (!g_ping.enabled)
        {
            g_ping.enabled = true;
            g_ping.l3_ok = true;
            g_ping.fail_streak = 0;
            g_ping.st = PING_ST_IDLE;
            g_ping.next_due = make_timeout_time_ms(1000);
        }

        if (g_ping.st == PING_ST_IDLE && absolute_time_diff_us(now, g_ping.next_due) <= 0)
        {
            ping_socket_ensure_open();
            
            // Check socket state before sending
            g_ping.socket_state = getSn_SR(SOCKET_PING);
            if (g_ping.socket_state != SOCK_IPRAW)
            {
                g_ping.last_fail_reason = PING_FAIL_SOCKET;
                g_ping.fail_streak++;
                if (g_ping.fail_streak >= PING_FAIL_THRESHOLD)
                    g_ping.l3_ok = false;
                g_ping.next_due = make_timeout_time_ms(PING_INTERVAL_MS);
                // Don't proceed if socket is bad
            }
            else
            {
                // Note: We don't flush old packets here to avoid blocking the main loop.
                // The ping_consume_reply_from function will only accept replies from the
                // expected gateway IP, so stale packets should be filtered out anyway.
                
                // Send ping request
                (void)ping_request(SOCKET_PING, net_info.gw);
                g_ping.send_attempts++;
                
                // ping_request always returns 0, but sendto inside it may fail
                // We can't easily check sendto result without modifying ping.c
                // For now, proceed and let timeout handle failures
                
                // Note: ping_request() uses static RandomID/SeqNum variables we can't access,
                // so we can't perfectly match reply ID/SeqNum. However, we flushed old packets
                // above, so any valid echo reply during our timeout window is likely our reply.
                
                g_ping.deadline = make_timeout_time_ms(PING_TIMEOUT_MS);
                g_ping.st = PING_ST_WAIT;
                g_ping.last_fail_reason = PING_FAIL_NONE;  // Reset failure reason
            }
        }
        else if (g_ping.st == PING_ST_WAIT)
        {
            // Check if socket is still valid before attempting to receive
            uint8_t sr = getSn_SR(SOCKET_PING);
            g_ping.socket_state = sr;
            
            if (sr != SOCK_IPRAW)
            {
                // Socket error - reset and try again later
                g_ping.last_fail_reason = PING_FAIL_SOCKET;
                g_ping.fail_streak++;
                if (g_ping.fail_streak >= PING_FAIL_THRESHOLD)
                    g_ping.l3_ok = false;
                ping_monitor_reset();
                g_ping.next_due = make_timeout_time_ms(PING_INTERVAL_MS);
            }
            else
            {
                // Only try to consume reply if we have data available
                // This avoids consuming packets unnecessarily
                int32_t rlen = getSn_RX_RSR(SOCKET_PING);
                g_ping.rx_bytes_waiting = rlen;
                g_ping.reply_attempts++;
                bool got_reply = false;
                
                if (rlen > 0)
                {
                    // Try to consume reply - this will consume the packet even if validation fails
                    got_reply = ping_consume_reply_from(SOCKET_PING, net_info.gw);
                    
                    // If we had data but didn't get a valid reply, the packet was consumed
                    // but validation failed (wrong type, wrong IP, etc.)
                    // The failure reason is set inside ping_consume_reply_from
                }
                
                if (got_reply)
                {
                    g_ping.fail_streak = 0;
                    g_ping.l3_ok = true;
                    g_ping.st = PING_ST_IDLE;
                    g_ping.next_due = make_timeout_time_ms(PING_INTERVAL_MS);
                    g_ping.last_fail_reason = PING_FAIL_NONE;
                }
                else if (absolute_time_diff_us(now, g_ping.deadline) <= 0)
                {
                    // still waiting for reply - update diagnostics
                    g_ping.rx_bytes_waiting = getSn_RX_RSR(SOCKET_PING);
                }
                else
                {
                    // timeout - no reply received
                    g_ping.last_fail_reason = PING_FAIL_TIMEOUT;
                    g_ping.fail_streak++;
                    if (g_ping.fail_streak >= PING_FAIL_THRESHOLD)
                        g_ping.l3_ok = false;

                    g_ping.st = PING_ST_IDLE;
                    g_ping.next_due = make_timeout_time_ms(PING_INTERVAL_MS);
                }
            }
        }
    }
    else
    {
        // Ping isn’t valid right now (no link or no lease). Keep it neutral.
        g_ping.enabled = false;
        g_ping.l3_ok = true;
        g_ping.fail_streak = 0;
        g_ping.st = PING_ST_IDLE;
    }

    // --- Consolidated offline decision
    const bool offline_now = (!g_phy_link_up) || (dhcp_leased && !g_ping.l3_ok);

    // Handle transitions to offline state
    if (!g_offline && offline_now)
    {
        // Record when offline state started
        g_offline_start_time = now;
        
        if (!g_phy_link_up)
            printf("[NET] PHY link DOWN (cable unplugged). Mode switch is %s.\n", switch_on ? "ON" : "OFF");
        else
            printf("[NET] Gateway ping FAILED (threshold=%d). Mode switch is %s.\n", PING_FAIL_THRESHOLD, switch_on ? "ON" : "OFF");
        
        printf("[NET] Offline state detected. Will shut down relays after %d seconds if switch is OFF.\n", OFFLINE_SHUTDOWN_DELAY_MS / 1000);
    }

    // Check if we should shut down relays (only if offline for >= threshold and switch is OFF)
    if (offline_now && !switch_on && g_offline_start_time != 0)
    {
        int64_t offline_duration_ms = absolute_time_diff_us(g_offline_start_time, now) / 1000;
        
        // Only shut down if we haven't already done so and threshold has passed
        if (offline_duration_ms >= OFFLINE_SHUTDOWN_DELAY_MS && !g_relay_state_has_saved)
        {
            // Save current relay states before shutting down (for restore on recovery)
            for (int i = 0; i < 4; i++)
            {
                g_relay_state_saved[i] = g_relay_state[i];
            }
            g_relay_state_has_saved = true;
            
            printf("[NET] Network offline for %lld ms (>= %d ms threshold). Switch is OFF - saving relay states and shutting down all relays.\n",
                   offline_duration_ms, OFFLINE_SHUTDOWN_DELAY_MS);
            printf("[NET] Saved relay states: [%d %d %d %d]\n",
                   g_relay_state_saved[0] ? 1 : 0,
                   g_relay_state_saved[1] ? 1 : 0,
                   g_relay_state_saved[2] ? 1 : 0,
                   g_relay_state_saved[3] ? 1 : 0);
            
            relay_all_apply(false);  // Turn off all relays
        }
    }
    else if (offline_now && switch_on)
    {
        // Switch is ON - don't save states, relays remain as-is
        g_relay_state_has_saved = false;
    }

    // Handle recovery from offline state
    if (g_offline && !offline_now)
    {
        // Reset offline start time
        g_offline_start_time = 0;
        
        printf("[NET] Connectivity restored (link up + gateway reachable).\n");
        
        // If we have saved relay states (from previous shutdown), restore them
        if (g_relay_state_has_saved)
        {
            printf("[NET] Restoring saved relay states: [%d %d %d %d]\n",
                   g_relay_state_saved[0] ? 1 : 0,
                   g_relay_state_saved[1] ? 1 : 0,
                   g_relay_state_saved[2] ? 1 : 0,
                   g_relay_state_saved[3] ? 1 : 0);
            
            // Restore each relay to its saved state
            for (int i = 0; i < 4; i++)
            {
                relay_apply(i, g_relay_state_saved[i]);
            }
            
            // Clear the saved state flag after restore
            g_relay_state_has_saved = false;
            printf("[NET] Relay states restored successfully.\n");
        }
        else
        {
            printf("[NET] No saved relay states to restore (relays remain in current state).\n");
        }
    }

    g_offline = offline_now;
}

/* Flash storage functions for relay states */
static uint32_t relay_state_calculate_checksum(const relay_state_flash_t *data)
{
    uint32_t sum = 0;
    const uint8_t *bytes = (const uint8_t *)data;
    for (size_t i = 0; i < offsetof(relay_state_flash_t, checksum); i++)
    {
        sum += bytes[i];
    }
    return sum;
}

static void relay_state_load_from_flash(void)
{
    relay_state_flash_t flash_data;
    const uint8_t *flash_ptr = (const uint8_t *)(XIP_BASE + RELAY_STATE_FLASH_OFFSET);
    
    // Read from flash (XIP - execute in place)
    memcpy(&flash_data, flash_ptr, sizeof(relay_state_flash_t));
    
    // Validate magic number and version
    if (flash_data.magic != RELAY_STATE_MAGIC || flash_data.version != RELAY_STATE_VERSION)
    {
        printf("[FLASH] No valid relay state data in flash (magic=0x%08X, version=%d). Using defaults.\n",
               flash_data.magic, flash_data.version);
        return;
    }
    
    // Validate checksum
    uint32_t calculated_checksum = relay_state_calculate_checksum(&flash_data);
    if (calculated_checksum != flash_data.checksum)
    {
        printf("[FLASH] Relay state checksum mismatch (got 0x%08X, expected 0x%08X). Using defaults.\n",
               calculated_checksum, flash_data.checksum);
        return;
    }
    
    // Load relay states
    for (int i = 0; i < 4; i++)
    {
        g_relay_state[i] = flash_data.relay_state[i];
    }
    
    printf("[FLASH] Loaded relay states from flash: [%d %d %d %d]\n",
           g_relay_state[0] ? 1 : 0,
           g_relay_state[1] ? 1 : 0,
           g_relay_state[2] ? 1 : 0,
           g_relay_state[3] ? 1 : 0);
}

static void relay_state_save_to_flash(void)
{
    const absolute_time_t now = get_absolute_time();
    
    // Debounce: don't save too frequently
    if (g_last_flash_save_time != 0)
    {
        int64_t elapsed_ms = absolute_time_diff_us(g_last_flash_save_time, now) / 1000;
        if (elapsed_ms < FLASH_SAVE_DEBOUNCE_MS)
        {
            // Too soon, skip this save
            return;
        }
    }
    
    g_last_flash_save_time = now;
    
    // Prepare data structure
    relay_state_flash_t flash_data;
    flash_data.magic = RELAY_STATE_MAGIC;
    flash_data.version = RELAY_STATE_VERSION;
    for (int i = 0; i < 4; i++)
    {
        flash_data.relay_state[i] = g_relay_state[i];
    }
    flash_data.checksum = relay_state_calculate_checksum(&flash_data);
    
    // Flash operations must be done with interrupts disabled and from RAM
    // We need to erase the sector first, then program it
    uint32_t ints = save_and_disable_interrupts();
    
    // Erase the sector (4096 bytes)
    flash_range_erase(RELAY_STATE_FLASH_OFFSET, FLASH_SECTOR_SIZE);
    
    // Program the data (must be page-aligned, 256 bytes)
    // We'll write our structure and pad to page size
    uint8_t page_buffer[FLASH_PAGE_SIZE];
    memset(page_buffer, 0xFF, FLASH_PAGE_SIZE);
    memcpy(page_buffer, &flash_data, sizeof(relay_state_flash_t));
    
    flash_range_program(RELAY_STATE_FLASH_OFFSET, page_buffer, FLASH_PAGE_SIZE);
    
    restore_interrupts(ints);
    
    printf("[FLASH] Saved relay states to flash: [%d %d %d %d]\n",
           g_relay_state[0] ? 1 : 0,
           g_relay_state[1] ? 1 : 0,
           g_relay_state[2] ? 1 : 0,
           g_relay_state[3] ? 1 : 0);
}

/* Relay HW */
static void relay_hw_init(void)
{
    // Load relay states from flash first
    relay_state_load_from_flash();
    
    // Initialize GPIO and apply loaded states
    for (int i = 0; i < 4; i++)
    {
        gpio_init(g_relay_pins[i]);
        gpio_set_dir(g_relay_pins[i], GPIO_OUT);

        // Apply loaded state (or default OFF if flash was empty)
        const bool level = g_relay_state[i] ? (RELAY_ACTIVE_LEVEL ? 1 : 0)
                                            : (RELAY_ACTIVE_LEVEL ? 0 : 1);
        gpio_put(g_relay_pins[i], level);
        
        // Update indicator LEDs
        ext_led_update_relay_indicator(i, g_relay_state[i]);
    }
}

static void relay_apply(int idx, bool on)
{
    if (idx < 0 || idx > 3) return;
    
    // Only save if state actually changed
    if (g_relay_state[idx] == on)
        return;
    
    g_relay_state[idx] = on;

    const bool level = on ? (RELAY_ACTIVE_LEVEL ? 1 : 0)
                          : (RELAY_ACTIVE_LEVEL ? 0 : 1);

    gpio_put(g_relay_pins[idx], level);

    // Relay indicator LEDs 2..5 track relay states
    ext_led_update_relay_indicator(idx, on);
    
    // Save to flash (with debouncing)
    relay_state_save_to_flash();
}

static void relay_toggle(int idx)
{
    if (idx < 0 || idx > 3) return;
    relay_apply(idx, !g_relay_state[idx]);
}

static void relay_all_apply(bool on)
{
    for (int i = 0; i < 4; i++) relay_apply(i, on);
}

static void relay_all_toggle(void)
{
    for (int i = 0; i < 4; i++) relay_toggle(i);
}

/*
 * This function is called by the patched httpUtil.c:
 * predefined_get_cgi_processor() validates the API key and then calls us with:
 * endpoint = "relay1/on", "all/state", etc.
 *
 * Return value:
 *  1 -> handled (buf/len filled)
 *  0 -> not handled (http server will treat as missing)
 */
uint8_t control_system_http_handle(const char *endpoint, uint8_t *buf, uint16_t *len)
{
    if (!endpoint || !buf || !len) return 0;

    // relayN/on|off|toggle|state
    if (strncmp(endpoint, "relay", 5) == 0)
    {
        // expects relay1/... relay2/... relay3/... relay4/...
        char n = endpoint[5];
        int r = (int)(n - '1'); // '1'..'4' -> 0..3
        if (r < 0 || r > 3) return 0;

        const char *p = endpoint + 6; // after "relayN"
        if (*p != '/') return 0;
        p++;

        if (strcmp(p, "on") == 0)
        {
            relay_apply(r, true);
            *len = (uint16_t)sprintf((char*)buf, "OK relay%d ON\n", r + 1);
            return 1;
        }
        if (strcmp(p, "off") == 0)
        {
            relay_apply(r, false);
            *len = (uint16_t)sprintf((char*)buf, "OK relay%d OFF\n", r + 1);
            return 1;
        }
        if (strcmp(p, "toggle") == 0)
        {
            relay_toggle(r);
            *len = (uint16_t)sprintf((char*)buf, "OK relay%d %s\n", r + 1, g_relay_state[r] ? "ON" : "OFF");
            return 1;
        }
        if (strcmp(p, "state") == 0)
        {
            *len = (uint16_t)sprintf((char*)buf, "%d\n", g_relay_state[r] ? 1 : 0);
            return 1;
        }

        return 0;
    }

    // all/on|off|toggle|state
    if (strncmp(endpoint, "all/", 4) == 0)
    {
        const char *p = endpoint + 4;

        if (strcmp(p, "on") == 0)
        {
            relay_all_apply(true);
            *len = (uint16_t)sprintf((char*)buf, "OK all ON\n");
            return 1;
        }
        if (strcmp(p, "off") == 0)
        {
            relay_all_apply(false);
            *len = (uint16_t)sprintf((char*)buf, "OK all OFF\n");
            return 1;
        }
        if (strcmp(p, "toggle") == 0)
        {
            relay_all_toggle();
            *len = (uint16_t)sprintf((char*)buf, "OK all toggled\n");
            return 1;
        }
        if (strcmp(p, "state") == 0)
        {
            *len = (uint16_t)sprintf((char*)buf, "%d%d%d%d\n",
                                     g_relay_state[0] ? 1 : 0,
                                     g_relay_state[1] ? 1 : 0,
                                     g_relay_state[2] ? 1 : 0,
                                     g_relay_state[3] ? 1 : 0);
            return 1;
        }
        return 0;
    }

    // debug - return debug information as JSON (same pattern as relay endpoints)
    if (strcmp(endpoint, "debug") == 0)
    {
        // Get current socket state for diagnostics
        uint8_t current_socket_state = getSn_SR(SOCKET_PING);
        int32_t current_rx_bytes = getSn_RX_RSR(SOCKET_PING);
        
        // Calculate time until next ping or time since deadline
        int64_t time_info = 0;
        absolute_time_t now = get_absolute_time();
        if (g_ping.st == PING_ST_IDLE && g_ping.enabled)
        {
            int64_t diff_us = absolute_time_diff_us(now, g_ping.next_due);
            time_info = (diff_us > 0) ? (diff_us / 1000) : 0;  // ms until next ping
        }
        else if (g_ping.st == PING_ST_WAIT)
        {
            int64_t diff_us = absolute_time_diff_us(now, g_ping.deadline);
            time_info = (diff_us > 0) ? (diff_us / 1000) : (-diff_us / 1000);  // ms past deadline (negative = still waiting)
        }
        
        const char* fail_reason_str = "NONE";
        switch (g_ping.last_fail_reason)
        {
            case PING_FAIL_SOCKET: fail_reason_str = "SOCKET_ERROR"; break;
            case PING_FAIL_SEND: fail_reason_str = "SEND_FAILED"; break;
            case PING_FAIL_TIMEOUT: fail_reason_str = "TIMEOUT"; break;
            case PING_FAIL_WRONG_REPLY: fail_reason_str = "WRONG_REPLY"; break;
            case PING_FAIL_NONE: fail_reason_str = "NONE"; break;
        }
        
        const char* socket_state_str = "UNKNOWN";
        switch (current_socket_state)
        {
            case SOCK_CLOSED: socket_state_str = "CLOSED"; break;
            case SOCK_IPRAW: socket_state_str = "IPRAW"; break;
            default: socket_state_str = "OTHER"; break;
        }
        
        // Return JSON with network and ping status
        *len = (uint16_t)sprintf((char*)buf,
            "{\n"
            "  \"network\": {\n"
            "    \"ip\": \"%d.%d.%d.%d\",\n"
            "    \"subnet\": \"%d.%d.%d.%d\",\n"
            "    \"gateway\": \"%d.%d.%d.%d\",\n"
            "    \"dns\": \"%d.%d.%d.%d\",\n"
            "    \"mac\": \"%02X:%02X:%02X:%02X:%02X:%02X\"\n"
            "  },\n"
            "  \"phy\": {\n"
            "    \"link\": \"%s\"\n"
            "  },\n"
            "  \"ping\": {\n"
            "    \"enabled\": %s,\n"
            "    \"state\": \"%s\",\n"
            "    \"l3_ok\": %s,\n"
            "    \"fail_streak\": %d,\n"
            "    \"last_fail_reason\": \"%s\",\n"
            "    \"interval_ms\": %d,\n"
            "    \"timeout_ms\": %d,\n"
            "    \"fail_threshold\": %d,\n"
            "    \"socket_state\": \"%s\",\n"
            "    \"rx_bytes_waiting\": %d,\n"
            "    \"send_attempts\": %d,\n"
            "    \"reply_attempts\": %d,\n"
            "    \"time_info_ms\": %lld,\n"
            "    \"last_received\": {\n"
            "      \"ip\": \"%d.%d.%d.%d\",\n"
            "      \"type\": %d,\n"
            "      \"len\": %d\n"
            "    }\n"
            "  },\n"
            "  \"connectivity\": {\n"
            "    \"offline\": %s,\n"
            "    \"http_server\": \"%s\"\n"
            "  },\n"
            "  \"system\": {\n"
            "    \"switch\": \"%s\",\n"
            "    \"relays\": [%d, %d, %d, %d]\n"
            "  }\n"
            "}\n",
            net_info.ip[0], net_info.ip[1], net_info.ip[2], net_info.ip[3],
            net_info.sn[0], net_info.sn[1], net_info.sn[2], net_info.sn[3],
            net_info.gw[0], net_info.gw[1], net_info.gw[2], net_info.gw[3],
            net_info.dns[0], net_info.dns[1], net_info.dns[2], net_info.dns[3],
            net_info.mac[0], net_info.mac[1], net_info.mac[2], net_info.mac[3], net_info.mac[4], net_info.mac[5],
            g_phy_link_up ? "UP" : "DOWN",
            g_ping.enabled ? "true" : "false",
            (g_ping.st == PING_ST_IDLE) ? "IDLE" : "WAIT",
            g_ping.l3_ok ? "true" : "false",
            g_ping.fail_streak,
            fail_reason_str,
            PING_INTERVAL_MS,
            PING_TIMEOUT_MS,
            PING_FAIL_THRESHOLD,
            socket_state_str,
            (int)current_rx_bytes,
            g_ping.send_attempts,
            g_ping.reply_attempts,
            (long long)time_info,
            g_ping.last_received_ip[0], g_ping.last_received_ip[1], 
            g_ping.last_received_ip[2], g_ping.last_received_ip[3],
            (int)g_ping.last_received_type,
            (int)g_ping.last_received_len,
            g_offline ? "true" : "false",
            g_http_started ? "Running" : "Stopped",
            switch_is_on() ? "ON" : "OFF",
            g_relay_state[0] ? 1 : 0, g_relay_state[1] ? 1 : 0, g_relay_state[2] ? 1 : 0, g_relay_state[3] ? 1 : 0);
        return 1;
    }

    return 0;
}

/* Timer callback signature MUST be void(void) for wizchip_1ms_timer_initialize */
static void repeating_timer_callback(void)
{
    g_msec_cnt++;

    if (g_msec_cnt >= 1000 - 1) {
        g_msec_cnt = 0;
        DHCP_time_handler();
        DNS_time_handler();
    }
}

static void wizchip_dhcp_init(void)
{
    printf("DHCP client running\n");
    DHCP_init(SOCKET_DHCP, g_ethernet_buf);
    reg_dhcp_cbfunc(wizchip_dhcp_assign, wizchip_dhcp_assign, wizchip_dhcp_conflict);
}

static void wizchip_dhcp_assign(void)
{
    getIPfromDHCP(net_info.ip);
    getGWfromDHCP(net_info.gw);
    getSNfromDHCP(net_info.sn);
    getDNSfromDHCP(net_info.dns);

    net_info.dhcp = NETINFO_DHCP;

    network_initialize(net_info);
    print_network_information(net_info);

    printf("DHCP lease time: %ld seconds\n", getDHCPLeasetime());

    g_dhcp_get_ip_flag = 1;
}

static void wizchip_dhcp_conflict(void)
{
    printf("Conflict IP from DHCP\n");
    while (1) { tight_loop_contents(); }
}

static void start_http_once(void)
{
    if (g_http_started) return;

    httpServer_init(g_http_send_buf, g_http_recv_buf, HTTP_SOCKET_MAX_NUM, g_http_socket_num_list);
    reg_httpServer_webContent((uint8_t *)"index.html", (uint8_t *)index_page);

    printf("HTTP ready: http://%d.%d.%d.%d/index.html\n",
           net_info.ip[0], net_info.ip[1], net_info.ip[2], net_info.ip[3]);

    // Relay endpoints will be served via CGI routing in patched httpParser/httpUtil:
    //   http://<ip>/<APIKEY>/relay1/on
    //   http://<ip>/<APIKEY>/all/state
    // etc.

    g_http_started = 1;
}

int main(void)
{
    stdio_init_all();
    sleep_ms(3000);

    set_unique_mac(&net_info);

#if defined(PICO_DEFAULT_LED_PIN)
    gpio_init(PICO_DEFAULT_LED_PIN);
    gpio_set_dir(PICO_DEFAULT_LED_PIN, GPIO_OUT);
    gpio_put(PICO_DEFAULT_LED_PIN, 0);
#endif

    // Relay GPIO init (unchanged)
    relay_hw_init();

    // New peripherals
    ext_leds_init();
    switch_init();
    reset_button_init();

    // Boot LED sequence: external LEDs 1..5 (0.5s each)
    ext_led_boot_sequence();

    // After boot sequence: default OFF unless rules apply
    ext_led_set_idx(0, false);
    ext_led_sync_relays();

    // Status LED starts in DHCP wait mode
    status_led1_set_mode(NET_STATE_WAIT_DHCP);

    /* WIZnet bring-up (match other examples) */
    wizchip_spi_initialize();
    wizchip_cris_initialize();

    wizchip_reset();
    wizchip_initialize();
    wizchip_check();

    wizchip_delay_ms(2000);

    // Start PHY polling immediately
    g_next_phy_poll = get_absolute_time();

    /* Timer + DHCP/DNS init */
    wizchip_1ms_timer_initialize(repeating_timer_callback);
    wizchip_dhcp_init();
    DNS_init(SOCKET_DNS, g_ethernet_buf);

    while (1)
    {
        /* Keep DHCP running until leased (and after, for renewals) */
        int dhcp_ret = DHCP_run();

        const bool switch_on = switch_is_on();

        const bool dhcp_leased_now = (dhcp_ret == DHCP_IP_LEASED) && (g_dhcp_get_ip_flag == 1);

        // Update physical link + upstream reachability state
        connectivity_monitors_tick(dhcp_leased_now, switch_on);

        // Onboard LED mirrors switch state
#if defined(PICO_DEFAULT_LED_PIN)
        gpio_put(PICO_DEFAULT_LED_PIN, switch_on ? 1 : 0);
#endif

        // Track whether we ever got a lease (for LOST behavior)
        if (dhcp_leased_now && !g_has_ever_leased)
            g_has_ever_leased = true;

        // Decide LED1 state with clear precedence:
        //  1) Offline (cable unplugged OR gateway unreachable)
        //  2) DHCP leased => ONLINE
        //  3) No lease yet => WAIT_DHCP (before first lease) / LOST (after first lease)
        net_state_t desired = NET_STATE_BOOT;

        if (g_offline)
            desired = NET_STATE_OFFLINE;
        else if (dhcp_leased_now)
            desired = NET_STATE_ONLINE;
        else
            desired = (!g_has_ever_leased) ? NET_STATE_WAIT_DHCP : NET_STATE_LOST;

        if (g_net_state != desired)
            status_led1_set_mode(desired);

        // HTTP should come up as soon as we have an IP lease (even if upstream is down)
        if (dhcp_leased_now)
            start_http_once();

        // Drive status LED blink timing (if in blink mode)
        status_led1_update();

        // Check reset button (must be held for 1 second to reset relays)
        reset_button_tick();

        /* HTTP server main loop
         * Run only when the physical link is up (avoids socket churn when cable is removed).
         */
        if (g_http_started && g_phy_link_up)
        {
            for (uint8_t i = 0; i < HTTP_SOCKET_MAX_NUM; i++)
            {
                httpServer_run(i);
            }
        }

        sleep_ms(1);
    }
}
