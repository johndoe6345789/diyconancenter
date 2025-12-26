cmake_minimum_required(VERSION 3.15)
project(test_package CXX)

find_package(pdf-generator REQUIRED CONFIG)

add_executable(test_package test_package.cpp)
target_link_libraries(test_package pdf_generator::pdf_generator)
target_compile_features(test_package PRIVATE cxx_std_17)
