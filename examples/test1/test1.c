#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>

#include "pico/stdlib.h"
#include "hardware/gpio.h"

#include "port_common.h"

#include "wizchip_conf.h"
#include "wizchip_spi.h"

#include "dhcp.h"
#include "dns.h"
#include "timer.h"

#include "httpServer.h"
#include "web_page.h"

/* Buffer */
#define ETHERNET_BUF_MAX_SIZE (1024 * 2)

/* Sockets */
#define SOCKET_DHCP 0
#define SOCKET_DNS  1

/* Put HTTP on different sockets than DHCP/DNS */
#define HTTP_SOCKET_MAX_NUM 2
static uint8_t g_http_socket_num_list[HTTP_SOCKET_MAX_NUM] = {2, 3};

/* Network */
static wiz_NetInfo g_net_info = {
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

/* Common buffer (DHCP/DNS need this) */
static uint8_t g_ethernet_buf[ETHERNET_BUF_MAX_SIZE] = {0};

/* HTTP buffers */
static uint8_t g_http_send_buf[ETHERNET_BUF_MAX_SIZE] = {0};
static uint8_t g_http_recv_buf[ETHERNET_BUF_MAX_SIZE] = {0};

/* Flags */
static uint8_t g_dhcp_get_ip_flag = 0;
static uint8_t g_http_started = 0;

/* Timer */
static volatile uint16_t g_msec_cnt = 0;

/* DHCP callbacks */
static void wizchip_dhcp_assign(void);
static void wizchip_dhcp_conflict(void);

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
    getIPfromDHCP(g_net_info.ip);
    getGWfromDHCP(g_net_info.gw);
    getSNfromDHCP(g_net_info.sn);
    getDNSfromDHCP(g_net_info.dns);

    g_net_info.dhcp = NETINFO_DHCP;

    network_initialize(g_net_info);
    print_network_information(g_net_info);

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
           g_net_info.ip[0], g_net_info.ip[1], g_net_info.ip[2], g_net_info.ip[3]);

    g_http_started = 1;
}

int main(void)
{
    stdio_init_all();
    sleep_ms(3000);

#if defined(PICO_DEFAULT_LED_PIN)
    gpio_init(PICO_DEFAULT_LED_PIN);
    gpio_set_dir(PICO_DEFAULT_LED_PIN, GPIO_OUT);
    gpio_put(PICO_DEFAULT_LED_PIN, 0);
#endif

    /* WIZnet bring-up (match other examples) */
    wizchip_spi_initialize();
    wizchip_cris_initialize();

    wizchip_reset();
    wizchip_initialize();
    wizchip_check();

    wizchip_delay_ms(2000);

    /* Timer + DHCP/DNS init */
    wizchip_1ms_timer_initialize(repeating_timer_callback);
    wizchip_dhcp_init();
    DNS_init(SOCKET_DNS, g_ethernet_buf);

    absolute_time_t next_led_toggle = make_timeout_time_ms(500);
    bool led_state = false;

    while (1)
    {
        /* Keep DHCP running until leased (and after, for renewals) */
        int dhcp_ret = DHCP_run();

        if ((dhcp_ret == DHCP_IP_LEASED) && (g_dhcp_get_ip_flag == 1))
        {
            start_http_once();

#if defined(PICO_DEFAULT_LED_PIN)
            if (absolute_time_diff_us(get_absolute_time(), next_led_toggle) <= 0)
            {
                led_state = !led_state;
                gpio_put(PICO_DEFAULT_LED_PIN, led_state ? 1 : 0);
                next_led_toggle = make_timeout_time_ms(500);
            }
#endif
        }

        /* HTTP server main loop */
        if (g_http_started)
        {
            for (uint8_t i = 0; i < HTTP_SOCKET_MAX_NUM; i++)
            {
                httpServer_run(i);
            }
        }

        sleep_ms(1);
    }
}
