add_executable(test1
    test1.c
)

target_include_directories(test1 PRIVATE
    ${CMAKE_CURRENT_LIST_DIR}
)

target_link_libraries(test1
    pico_stdlib
    hardware_spi
    hardware_dma
    ETHERNET_FILES
    IOLIBRARY_FILES
    DHCP_FILES
    DNS_FILES
    TIMER_FILES
    HTTPSERVER_FILES
)

pico_enable_stdio_usb(test1 1)
pico_enable_stdio_uart(test1 1)
pico_add_extra_outputs(test1)
