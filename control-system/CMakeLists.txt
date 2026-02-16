add_executable(control_system
    control-system.c
)

target_include_directories(control_system PRIVATE
    ${CMAKE_CURRENT_LIST_DIR}
)

target_link_libraries(control_system
    pico_stdlib
    hardware_spi
    hardware_dma
    ETHERNET_FILES
    IOLIBRARY_FILES
    DHCP_FILES
    DNS_FILES
    TIMER_FILES
    HTTPSERVER_FILES
    PING_FILES
)

pico_enable_stdio_usb(control_system 1)
pico_enable_stdio_uart(control_system 1)
pico_add_extra_outputs(control_system)
