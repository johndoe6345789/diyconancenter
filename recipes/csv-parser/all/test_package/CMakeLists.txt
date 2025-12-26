cmake_minimum_required(VERSION 3.15)
project(test_package CXX)

find_package(csv-parser REQUIRED CONFIG)

add_executable(test_package test_package.cpp)
target_link_libraries(test_package csv_parser::csv_parser)
target_compile_features(test_package PRIVATE cxx_std_17)
