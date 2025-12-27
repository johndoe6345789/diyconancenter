cmake_minimum_required(VERSION 3.15)
project(encryption CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# Find Libsodium
find_package(libsodium REQUIRED CONFIG)

add_library(encryption src/encryption.cpp)

target_include_directories(encryption PUBLIC
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
    $<INSTALL_INTERFACE:include>
)

# Link to Libsodium
target_link_libraries(encryption PUBLIC libsodium::libsodium)

install(TARGETS encryption
    ARCHIVE DESTINATION lib
    LIBRARY DESTINATION lib
    RUNTIME DESTINATION bin
)

install(DIRECTORY include/ DESTINATION include)
