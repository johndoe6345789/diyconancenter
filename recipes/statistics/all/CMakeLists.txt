cmake_minimum_required(VERSION 3.15)
project(statistics CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# Find Boost
find_package(Boost REQUIRED CONFIG)

add_library(statistics src/statistics.cpp)

target_include_directories(statistics PUBLIC
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
    $<INSTALL_INTERFACE:include>
)

# Link to Boost (header-only accumulators library)
target_link_libraries(statistics PUBLIC Boost::headers)

install(TARGETS statistics
    ARCHIVE DESTINATION lib
    LIBRARY DESTINATION lib
    RUNTIME DESTINATION bin
)

install(DIRECTORY include/ DESTINATION include)
