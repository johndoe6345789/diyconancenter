#!/usr/bin/env python3
"""
Update test packages for libraries that now use real sources.
"""

import sys
from pathlib import Path

# Add the scripts directory to the path
sys.path.insert(0, str(Path(__file__).parent))
from real_libraries_mapping import get_library_info, get_all_real_packages


TEST_PACKAGE_CONFIGS = {
    "json-parser": {
        "include": "#include <nlohmann/json.hpp>",
        "test_code": '''    try {
        // Create a JSON object using nlohmann_json
        nlohmann::json j;
        j["name"] = "DIY Conan Center";
        j["version"] = "3.11.3";
        j["real_library"] = true;
        
        std::string json_str = j.dump();
        std::cout << "JSON created: " << json_str << std::endl;
        
        auto parsed = nlohmann::json::parse(json_str);
        if (parsed["real_library"] == true) {
            std::cout << "Test passed: json-parser (nlohmann_json) is working!" << std::endl;
            return 0;
        }
    } catch (const std::exception& e) {
        std::cerr << "Test failed: " << e.what() << std::endl;
        return 1;
    }''',
        "cmake_package": "nlohmann_json",
        "cmake_target": "nlohmann_json::nlohmann_json"
    },
    "logger": {
        "include": "#include <spdlog/spdlog.h>",
        "test_code": '''    try {
        spdlog::info("Test message from spdlog");
        spdlog::warn("Warning message");
        std::cout << "Test passed: logger (spdlog) is working!" << std::endl;
        return 0;
    } catch (const std::exception& e) {
        std::cerr << "Test failed: " << e.what() << std::endl;
        return 1;
    }''',
        "cmake_package": "spdlog",
        "cmake_target": "spdlog::spdlog"
    },
}


def create_test_cpp(package_name, config):
    """Create a test_package.cpp for a real library."""
    return f'''{config["include"]}
#include <iostream>

int main() {{
{config["test_code"]}
    return 1;
}}
'''


def create_test_cmake(package_name, config):
    """Create CMakeLists.txt for test package."""
    return f'''cmake_minimum_required(VERSION 3.15)
project(test_package CXX)

find_package({config["cmake_package"]} REQUIRED CONFIG)

add_executable(test_package test_package.cpp)
target_link_libraries(test_package {config["cmake_target"]})
target_compile_features(test_package PRIVATE cxx_std_17)
'''


def update_test_package(recipes_dir, package_name, config):
    """Update test package for a library that uses real sources."""
    test_package_dir = recipes_dir / package_name / "all" / "test_package"
    
    if not test_package_dir.exists():
        print(f"Warning: Test package directory for {package_name} not found")
        return False
    
    # Update test_package.cpp
    cpp_file = test_package_dir / "test_package.cpp"
    with open(cpp_file, 'w') as f:
        f.write(create_test_cpp(package_name, config))
    
    # Update CMakeLists.txt
    cmake_file = test_package_dir / "CMakeLists.txt"
    with open(cmake_file, 'w') as f:
        f.write(create_test_cmake(package_name, config))
    
    print(f"✓ Updated test package for {package_name}")
    return True


def main():
    """Main function."""
    repo_root = Path(__file__).parent.parent
    recipes_dir = repo_root / "recipes"
    
    print("=" * 70)
    print("Updating test packages for real libraries")
    print("=" * 70)
    print()
    
    updated = 0
    for package_name, config in TEST_PACKAGE_CONFIGS.items():
        if update_test_package(recipes_dir, package_name, config):
            updated += 1
    
    print()
    print(f"Updated {updated} test packages")
    print()
    print("Note: Only packages with specific test configurations were updated.")
    print("Other packages still use generic test code that may need manual updates.")
    
    return 0


if __name__ == "__main__":
    sys.exit(main())
