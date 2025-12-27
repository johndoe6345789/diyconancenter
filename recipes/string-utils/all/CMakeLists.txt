cmake_minimum_required(VERSION 3.15)
project(string-utils CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# Find Boost
find_package(Boost REQUIRED CONFIG)

add_library(string_utils src/string_utils.cpp)

target_include_directories(string_utils PUBLIC
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
    $<INSTALL_INTERFACE:include>
)

# Link to Boost (header-only algorithm/string library)
target_link_libraries(string_utils PUBLIC Boost::headers)

install(TARGETS string_utils
    ARCHIVE DESTINATION lib
    LIBRARY DESTINATION lib
    RUNTIME DESTINATION bin
)

install(DIRECTORY include/ DESTINATION include)
