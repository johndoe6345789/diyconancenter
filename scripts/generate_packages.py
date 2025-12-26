#!/usr/bin/env python3
"""Generate sample Conan package recipes."""

import os
from pathlib import Path

# Sample packages with their descriptions
PACKAGES = [
    ("json-parser", "A lightweight JSON parser library for C++", "1.0.0"),
    ("xml-parser", "Fast XML parsing library", "2.1.0"),
    ("yaml-config", "YAML configuration file parser", "1.5.2"),
    ("ini-reader", "Simple INI file reader and writer", "0.9.0"),
    ("csv-parser", "High-performance CSV file parser", "3.2.1"),
    ("logger", "Thread-safe logging library", "2.0.0"),
    ("crypto-utils", "Cryptographic utilities library", "1.3.0"),
    ("hash-functions", "Collection of hash functions", "1.1.0"),
    ("compression", "Data compression algorithms", "2.4.0"),
    ("string-utils", "String manipulation utilities", "1.0.5"),
    ("math-lib", "Mathematical functions library", "3.1.0"),
    ("vector-math", "Vector and matrix operations", "2.0.0"),
    ("geometry", "Geometric calculations library", "1.2.0"),
    ("statistics", "Statistical analysis functions", "1.0.0"),
    ("random-gen", "Random number generators", "2.1.0"),
    ("datetime-utils", "Date and time utilities", "1.4.0"),
    ("timer", "High-resolution timer library", "1.0.0"),
    ("threading", "Threading utilities and primitives", "2.3.0"),
    ("async-io", "Asynchronous I/O operations", "1.5.0"),
    ("network-lib", "Network communication library", "3.0.0"),
    ("http-client", "HTTP client library", "2.2.0"),
    ("websocket", "WebSocket implementation", "1.3.0"),
    ("tcp-server", "TCP server framework", "2.0.0"),
    ("udp-socket", "UDP socket wrapper", "1.1.0"),
    ("serialization", "Object serialization library", "2.1.0"),
    ("database-connector", "Database connection library", "1.8.0"),
    ("cache-manager", "In-memory cache management", "1.2.0"),
    ("queue", "Thread-safe queue implementations", "1.0.0"),
    ("stack", "Stack data structure utilities", "1.0.0"),
    ("tree", "Tree data structure library", "1.1.0"),
    ("graph", "Graph algorithms library", "2.0.0"),
    ("sorting", "Sorting algorithms collection", "1.0.0"),
    ("searching", "Search algorithms library", "1.0.0"),
    ("image-proc", "Image processing library", "3.5.0"),
    ("audio-codec", "Audio codec library", "2.1.0"),
    ("video-decoder", "Video decoding utilities", "1.9.0"),
    ("pdf-generator", "PDF generation library", "2.3.0"),
    ("barcode-reader", "Barcode reading library", "1.2.0"),
    ("qr-code", "QR code generation and reading", "1.4.0"),
    ("regex", "Regular expression library", "2.0.0"),
    ("template-engine", "Text template engine", "1.5.0"),
    ("markdown-parser", "Markdown to HTML converter", "2.2.0"),
    ("html-sanitizer", "HTML sanitization library", "1.1.0"),
    ("url-parser", "URL parsing and manipulation", "1.3.0"),
    ("email-validator", "Email address validation", "1.0.0"),
    ("jwt-auth", "JSON Web Token library", "2.1.0"),
    ("oauth-client", "OAuth 2.0 client library", "1.6.0"),
    ("encryption", "Encryption and decryption utilities", "2.0.0"),
    ("uuid-generator", "UUID generation library", "1.0.0"),
    ("cli-parser", "Command-line argument parser", "2.3.0"),
]

def create_conanfile(package_name, description, version):
    """Create a conanfile.py for a package."""
    return f'''from conan import ConanFile
from conan.tools.cmake import CMakeToolchain, CMake, cmake_layout


class {package_name.replace("-", "").title()}Conan(ConanFile):
    name = "{package_name}"
    version = "{version}"
    description = "{description}"
    license = "MIT"
    author = "DIY Conan Center"
    url = "https://github.com/johndoe6345789/diyconancenter"
    topics = ("c++", "library", "{package_name}")
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
    
    def layout(self):
        cmake_layout(self)
    
    def generate(self):
        tc = CMakeToolchain(self)
        tc.generate()
    
    def build(self):
        cmake = CMake(self)
        cmake.configure()
        cmake.build()
    
    def package(self):
        cmake = CMake(self)
        cmake.install()
    
    def package_info(self):
        self.cpp_info.libs = ["{package_name.replace("-", "_")}"]
'''

def create_conandata(version):
    """Create a conandata.yml file."""
    return f'''sources:
  "{version}":
    url: "https://github.com/example/example/archive/v{version}.tar.gz"
    sha256: "0000000000000000000000000000000000000000000000000000000000000000"
'''

def create_config(version):
    """Create a config.yml file."""
    return f'''versions:
  "{version}":
    folder: all
'''

def create_cmakelists(package_name):
    """Create a CMakeLists.txt file."""
    lib_name = package_name.replace("-", "_")
    return f'''cmake_minimum_required(VERSION 3.15)
project({package_name} CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

add_library({lib_name} src/{lib_name}.cpp)

target_include_directories({lib_name} PUBLIC
    $<BUILD_INTERFACE:${{CMAKE_CURRENT_SOURCE_DIR}}/include>
    $<INSTALL_INTERFACE:include>
)

install(TARGETS {lib_name}
    ARCHIVE DESTINATION lib
    LIBRARY DESTINATION lib
    RUNTIME DESTINATION bin
)

install(DIRECTORY include/ DESTINATION include)
'''

def create_header(package_name):
    """Create a header file."""
    lib_name = package_name.replace("-", "_")
    guard = f"{lib_name.upper()}_H"
    return f'''#ifndef {guard}
#define {guard}

namespace {lib_name} {{

class {lib_name.title().replace("_", "")} {{
public:
    {lib_name.title().replace("_", "")}();
    ~{lib_name.title().replace("_", "")}();
    
    void initialize();
    bool process();
}};

}} // namespace {lib_name}

#endif // {guard}
'''

def create_source(package_name):
    """Create a source file."""
    lib_name = package_name.replace("-", "_")
    return f'''#include "{lib_name}.h"
#include <iostream>

namespace {lib_name} {{

{lib_name.title().replace("_", "")}::{lib_name.title().replace("_", "")}() {{
    // Constructor
}}

{lib_name.title().replace("_", "")}::~{lib_name.title().replace("_", "")}() {{
    // Destructor
}}

void {lib_name.title().replace("_", "")}::initialize() {{
    std::cout << "Initializing {package_name}..." << std::endl;
}}

bool {lib_name.title().replace("_", "")}::process() {{
    std::cout << "Processing with {package_name}..." << std::endl;
    return true;
}}

}} // namespace {lib_name}
'''

def create_test_conanfile(package_name, version):
    """Create test_package/conanfile.py."""
    return f'''import os
from conan import ConanFile
from conan.tools.cmake import CMake, cmake_layout
from conan.tools.build import can_run


class {package_name.replace("-", "").title()}TestConan(ConanFile):
    settings = "os", "compiler", "build_type", "arch"
    generators = "CMakeDeps", "CMakeToolchain"

    def requirements(self):
        self.requires(self.tested_reference_str)

    def layout(self):
        cmake_layout(self)

    def build(self):
        cmake = CMake(self)
        cmake.configure()
        cmake.build()

    def test(self):
        if can_run(self):
            cmd = os.path.join(self.cpp.build.bindir, "test_package")
            self.run(cmd, env="conanrun")
'''

def create_test_cmakelists(package_name):
    """Create test_package/CMakeLists.txt."""
    lib_name = package_name.replace("-", "_")
    return f'''cmake_minimum_required(VERSION 3.15)
project(test_package CXX)

find_package({package_name} REQUIRED CONFIG)

add_executable(test_package test_package.cpp)
target_link_libraries(test_package {lib_name}::{lib_name})
target_compile_features(test_package PRIVATE cxx_std_17)
'''

def create_test_source(package_name):
    """Create test_package/test_package.cpp."""
    lib_name = package_name.replace("-", "_")
    return f'''#include <{lib_name}.h>
#include <iostream>

int main() {{
    {lib_name}::{lib_name.title().replace("_", "")} obj;
    obj.initialize();
    
    if (obj.process()) {{
        std::cout << "Test passed: {package_name} is working!" << std::endl;
        return 0;
    }}
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}}
'''

def create_package(base_path, package_name, description, version):
    """Create a complete package structure."""
    package_path = base_path / package_name
    all_path = package_path / "all"
    
    # Create directories
    all_path.mkdir(parents=True, exist_ok=True)
    (all_path / "src").mkdir(exist_ok=True)
    (all_path / "include").mkdir(exist_ok=True)
    (all_path / "test_package").mkdir(exist_ok=True)
    
    # Create files
    lib_name = package_name.replace("-", "_")
    
    # Recipe files
    with open(package_path / "config.yml", "w") as f:
        f.write(create_config(version))
    
    with open(all_path / "conanfile.py", "w") as f:
        f.write(create_conanfile(package_name, description, version))
    
    with open(all_path / "conandata.yml", "w") as f:
        f.write(create_conandata(version))
    
    with open(all_path / "CMakeLists.txt", "w") as f:
        f.write(create_cmakelists(package_name))
    
    # Source files
    with open(all_path / "include" / f"{lib_name}.h", "w") as f:
        f.write(create_header(package_name))
    
    with open(all_path / "src" / f"{lib_name}.cpp", "w") as f:
        f.write(create_source(package_name))
    
    # Test package
    with open(all_path / "test_package" / "conanfile.py", "w") as f:
        f.write(create_test_conanfile(package_name, version))
    
    with open(all_path / "test_package" / "CMakeLists.txt", "w") as f:
        f.write(create_test_cmakelists(package_name))
    
    with open(all_path / "test_package" / "test_package.cpp", "w") as f:
        f.write(create_test_source(package_name))
    
    print(f"Created package: {package_name} v{version}")

def main():
    """Main function."""
    repo_root = Path(__file__).parent.parent
    recipes_dir = repo_root / "recipes"
    recipes_dir.mkdir(exist_ok=True)
    
    print(f"Generating {len(PACKAGES)} sample packages...")
    
    for package_name, description, version in PACKAGES:
        create_package(recipes_dir, package_name, description, version)
    
    print(f"\nSuccessfully generated {len(PACKAGES)} packages in {recipes_dir}")

if __name__ == "__main__":
    main()
