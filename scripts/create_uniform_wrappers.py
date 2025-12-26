#!/usr/bin/env python3
"""
Create wrapper implementations that use real libraries as dependencies.
This maintains a uniform API while leveraging real library code.
"""

import sys
from pathlib import Path
import shutil


def create_wrapper_header(package_name, lib_name):
    """Create a uniform wrapper header."""
    class_name = lib_name.title().replace("_", "")
    guard = f"{lib_name.upper()}_H"
    
    return f'''#ifndef {guard}
#define {guard}

namespace {lib_name} {{

class {class_name} {{
public:
    {class_name}();
    ~{class_name}();
    
    void initialize();
    bool process();
    
private:
    class Impl;
    Impl* pImpl;
}};

}} // namespace {lib_name}

#endif // {guard}
'''


def create_wrapper_source_nlohmann_json(lib_name):
    """Create wrapper implementation using nlohmann_json."""
    class_name = lib_name.title().replace("_", "")
    
    return f'''#include "{lib_name}.h"
#include <nlohmann/json.hpp>
#include <iostream>

namespace {lib_name} {{

class {class_name}::Impl {{
public:
    nlohmann::json data;
}};

{class_name}::{class_name}() : pImpl(new Impl()) {{
    // Constructor
}}

{class_name}::~{class_name}() {{
    delete pImpl;
}}

void {class_name}::initialize() {{
    std::cout << "Initializing json-parser with nlohmann_json backend..." << std::endl;
    pImpl->data = nlohmann::json::object();
    pImpl->data["initialized"] = true;
}}

bool {class_name}::process() {{
    std::cout << "Processing with json-parser (nlohmann_json backend)..." << std::endl;
    pImpl->data["processed"] = true;
    std::string output = pImpl->data.dump();
    std::cout << "JSON: " << output << std::endl;
    return true;
}}

}} // namespace {lib_name}
'''


def create_wrapper_source_spdlog(lib_name):
    """Create wrapper implementation using spdlog."""
    class_name = lib_name.title().replace("_", "")
    
    return f'''#include "{lib_name}.h"
#include <spdlog/spdlog.h>
#include <iostream>

namespace {lib_name} {{

class {class_name}::Impl {{
public:
    // spdlog is header-only/singleton, no instance needed
}};

{class_name}::{class_name}() : pImpl(new Impl()) {{
    // Constructor
}}

{class_name}::~{class_name}() {{
    delete pImpl;
}}

void {class_name}::initialize() {{
    spdlog::info("Initializing logger with spdlog backend...");
}}

bool {class_name}::process() {{
    spdlog::info("Processing with logger (spdlog backend)...");
    spdlog::debug("Debug message");
    spdlog::warn("Warning message");
    return true;
}}

}} // namespace {lib_name}
'''


def create_conanfile_with_wrapper(package_name, info, lib_name):
    """Create conanfile that builds wrapper using real library."""
    class_name = package_name.replace("-", "").title()
    
    return f'''from conan import ConanFile
from conan.tools.cmake import CMakeToolchain, CMake, cmake_layout, CMakeDeps


class {class_name}Conan(ConanFile):
    name = "{package_name}"
    version = "{info['version']}"
    description = "Wrapper for {info['real_name']} with uniform API"
    license = "MIT"
    author = "DIY Conan Center"
    url = "https://github.com/johndoe6345789/diyconancenter"
    topics = ("c++", "library", "{package_name}", "{info['real_name']}")
    settings = "os", "compiler", "build_type", "arch"
    options = {{"shared": [True, False], "fPIC": [True, False]}}
    default_options = {{"shared": False, "fPIC": True}}
    exports_sources = "CMakeLists.txt", "src/*", "include/*"
    
    def config_options(self):
        if self.settings.os == "Windows":
            del self.options.fPIC
    
    def configure(self):
        if self.options.shared:
            self.options.rm_safe("fPIC")
    
    def requirements(self):
        # Depend on the real library from Conan Center
        self.requires("{info['conan_center_name']}/{info['version']}")
    
    def layout(self):
        cmake_layout(self)
    
    def generate(self):
        tc = CMakeToolchain(self)
        tc.generate()
        deps = CMakeDeps(self)
        deps.generate()
    
    def build(self):
        cmake = CMake(self)
        cmake.configure()
        cmake.build()
    
    def package(self):
        cmake = CMake(self)
        cmake.install()
    
    def package_info(self):
        self.cpp_info.libs = ["{lib_name}"]
'''


def create_cmake_with_dependency(package_name, conan_package, conan_target):
    """Create CMakeLists.txt that links to real library."""
    lib_name = package_name.replace("-", "_")
    
    return f'''cmake_minimum_required(VERSION 3.15)
project({package_name} CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# Find the real library
find_package({conan_package} REQUIRED CONFIG)

add_library({lib_name} src/{lib_name}.cpp)

target_include_directories({lib_name} PUBLIC
    $<BUILD_INTERFACE:${{CMAKE_CURRENT_SOURCE_DIR}}/include>
    $<INSTALL_INTERFACE:include>
)

# Link to the real library
target_link_libraries({lib_name} PUBLIC {conan_target})

install(TARGETS {lib_name}
    ARCHIVE DESTINATION lib
    LIBRARY DESTINATION lib
    RUNTIME DESTINATION bin
)

install(DIRECTORY include/ DESTINATION include)
'''


# Configurations for packages we want to wrap
WRAPPER_CONFIGS = {
    "json-parser": {
        "source_generator": create_wrapper_source_nlohmann_json,
        "cmake_package": "nlohmann_json",
        "cmake_target": "nlohmann_json::nlohmann_json",
    },
    "logger": {
        "source_generator": create_wrapper_source_spdlog,
        "cmake_package": "spdlog",
        "cmake_target": "spdlog::spdlog",
    },
}


def create_wrapper_package(recipes_dir, package_name, info, config):
    """Create a wrapper package with uniform API."""
    package_path = recipes_dir / package_name / "all"
    lib_name = package_name.replace("-", "_")
    
    if not package_path.exists():
        print(f"Warning: Package path {package_path} not found")
        return False
    
    print(f"Creating uniform wrapper for {package_name} using {info['real_name']}...")
    
    # Create directories if they don't exist
    (package_path / "src").mkdir(exist_ok=True)
    (package_path / "include").mkdir(exist_ok=True)
    
    # Create header file
    header_file = package_path / "include" / f"{lib_name}.h"
    with open(header_file, 'w') as f:
        f.write(create_wrapper_header(package_name, lib_name))
    
    # Create source file with real library implementation
    source_file = package_path / "src" / f"{lib_name}.cpp"
    with open(source_file, 'w') as f:
        f.write(config["source_generator"](lib_name))
    
    # Create conanfile
    conanfile = package_path / "conanfile.py"
    with open(conanfile, 'w') as f:
        f.write(create_conanfile_with_wrapper(package_name, info, lib_name))
    
    # Create CMakeLists.txt
    cmake_file = package_path / "CMakeLists.txt"
    with open(cmake_file, 'w') as f:
        f.write(create_cmake_with_dependency(package_name, config["cmake_package"], config["cmake_target"]))
    
    print(f"  ✓ Created uniform wrapper for {package_name}")
    return True


def main():
    """Main function."""
    repo_root = Path(__file__).parent.parent
    recipes_dir = repo_root / "recipes"
    
    # Import after setting up path
    sys.path.insert(0, str(Path(__file__).parent))
    from real_libraries_mapping import get_library_info
    
    print("=" * 70)
    print("Creating uniform wrappers with real library backends")
    print("=" * 70)
    print()
    
    updated = 0
    for package_name, config in WRAPPER_CONFIGS.items():
        info = get_library_info(package_name)
        if info and info.get('use_conan_center'):
            if create_wrapper_package(recipes_dir, package_name, info, config):
                updated += 1
        print()
    
    print("=" * 70)
    print(f"Created {updated} uniform wrapper packages")
    print("=" * 70)
    
    return 0


if __name__ == "__main__":
    sys.exit(main())
