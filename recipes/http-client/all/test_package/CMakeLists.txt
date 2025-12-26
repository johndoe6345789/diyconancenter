cmake_minimum_required(VERSION 3.15)
project(test_package CXX)

find_package(http-client REQUIRED CONFIG)

add_executable(test_package test_package.cpp)
target_link_libraries(test_package http_client::http_client)
target_compile_features(test_package PRIVATE cxx_std_17)
