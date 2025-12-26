cmake_minimum_required(VERSION 3.15)
project(json-parser CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# Find the real library
find_package(nlohmann_json REQUIRED CONFIG)

add_library(json_parser src/json_parser.cpp)

target_include_directories(json_parser PUBLIC
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
    $<INSTALL_INTERFACE:include>
)

# Link to the real library
target_link_libraries(json_parser PUBLIC nlohmann_json::nlohmann_json)

install(TARGETS json_parser
    ARCHIVE DESTINATION lib
    LIBRARY DESTINATION lib
    RUNTIME DESTINATION bin
)

install(DIRECTORY include/ DESTINATION include)
