cmake_minimum_required(VERSION 3.15)
project(math-lib CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# Find Boost
find_package(Boost REQUIRED CONFIG)

add_library(math_lib src/math_lib.cpp)

target_include_directories(math_lib PUBLIC
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
    $<INSTALL_INTERFACE:include>
)

# Link to Boost (header-only math library)
target_link_libraries(math_lib PUBLIC Boost::headers)

install(TARGETS math_lib
    ARCHIVE DESTINATION lib
    LIBRARY DESTINATION lib
    RUNTIME DESTINATION bin
)

install(DIRECTORY include/ DESTINATION include)
