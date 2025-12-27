# 🚀 DIY Conan Center

A personal C/C++ package repository powered by Conan and GitHub Actions, featuring 50 sample packages ready to use.

## 📦 What is This?

This is a DIY (Do-It-Yourself) Conan Center repository that demonstrates how to create and manage your own C/C++ package repository using:
- **Conan 2.x** - Modern C/C++ package manager
- **GitHub Actions** - Automated building and testing
- **GitHub Pages** - Beautiful package index and documentation

## 🌐 Browse Packages

Visit our [Package Index](https://johndoe6345789.github.io/diyconancenter/) to browse all available packages.

## 🔗 Real Library Integration

This repository demonstrates a **hybrid approach** to C/C++ package management:

### Approach 1: Uniform Wrapper Libraries (Recommended)

These packages provide a **uniform, predictable API** while using real production libraries as backends:

| Package Name | Uniform API | Backend Library | Conan Center Package |
|--------------|-------------|-----------------|---------------------|
| `json-parser` | `json_parser::JsonParser` | nlohmann_json | `nlohmann_json/3.11.3` |
| `logger` | `logger::Logger` | spdlog | `spdlog/1.13.0` |
| `string-utils` | `string_utils::StringUtils` | Boost.Algorithm.String | `boost/1.86.0` |
| `math-lib` | `math_lib::MathLib` | Boost.Math | `boost/1.86.0` |
| `statistics` | `statistics::Statistics` | Boost.Accumulators | `boost/1.86.0` |
| `queue` | `queue::Queue<T>` | Boost.Lockfree | `boost/1.86.0` |
| `encryption` | `encryption::Encryption` | Libsodium | `libsodium/1.0.20` |

**Benefits:**
- ✅ **Predictable API**: All packages follow the same pattern with `initialize()` and `process()` methods
- ✅ **Uniform classes**: Consistent naming and structure across all packages
- ✅ **Real implementations**: Uses production-ready libraries internally (via Pimpl pattern)
- ✅ **Easy to learn**: Once you know one package, you know them all

**Example usage:**
```cpp
#include <json_parser.h>

json_parser::JsonParser parser;
parser.initialize();
parser.process();  // Uses nlohmann_json internally
```

### Approach 2: Direct Conan Center Wrappers

These packages act as thin wrappers that directly pull from Conan Center:

| Package Name | Real Library | Conan Center Package | Upstream Repository |
|--------------|--------------|---------------------|---------------------|
| `xml-parser` | tinyxml2 | `tinyxml2/10.0.0` | [leethomason/tinyxml2](https://github.com/leethomason/tinyxml2) |
| `yaml-config` | yaml-cpp | `yaml-cpp/0.8.0` | [jbeder/yaml-cpp](https://github.com/jbeder/yaml-cpp) |
| `ini-reader` | inih | `inih/58` | [benhoyt/inih](https://github.com/benhoyt/inih) |
| `crypto-utils` | openssl | `openssl/3.2.0` | [openssl/openssl](https://github.com/openssl/openssl) |
| `compression` | zlib | `zlib/1.3.1` | [madler/zlib](https://github.com/madler/zlib) |
| `websocket` | websocketpp | `websocketpp/0.8.2` | [zaphoyd/websocketpp](https://github.com/zaphoyd/websocketpp) |
| `cli-parser` | CLI11 | `cli11/2.4.1` | [CLIUtils/CLI11](https://github.com/CLIUtils/CLI11) |
| `jwt-auth` | jwt-cpp | `jwt-cpp/0.7.0` | [Thalhammer/jwt-cpp](https://github.com/Thalhammer/jwt-cpp) |
| `datetime-utils` | date | `date/3.0.1` | [HowardHinnant/date](https://github.com/HowardHinnant/date) |
| `regex` | re2 | `re2/2023-11-01` | [google/re2](https://github.com/google/re2) |
| `image-proc` | stb | `stb/master` | [nothings/stb](https://github.com/nothings/stb) |

### Approach 3: Git Source Fetching

These packages download source code directly from upstream repositories:

| Package Name | Real Library | Version | Upstream Repository |
|--------------|--------------|---------|---------------------|
| `csv-parser` | csv-parser | 2.3.0 | [vincentlaucsb/csv-parser](https://github.com/vincentlaucsb/csv-parser) |
| `http-client` | cpp-httplib | 0.15.3 | [yhirose/cpp-httplib](https://github.com/yhirose/cpp-httplib) |
| `hash-functions` | hash-library | 8 | [stbrumme/hash-library](https://github.com/stbrumme/hash-library) |
| `uuid-generator` | stduuid | 1.2.3 | [mariusbancila/stduuid](https://github.com/mariusbancila/stduuid) |
| `email-validator` | email-validator | 1.0.0 | [JulianSchmid/cpp-email-validator](https://github.com/JulianSchmid/cpp-email-validator) |
| `markdown-parser` | md4c | 0.5.2 | [mity/md4c](https://github.com/mity/md4c) |

### DIY/Stub Implementations

The remaining packages (~26) are simple DIY implementations useful for demonstration and testing purposes.

## 📚 Available Packages (50 Total)

This repository includes 50 sample packages covering various categories:

### Parsing & Configuration
- `json-parser` - Lightweight JSON parser library
- `xml-parser` - Fast XML parsing library
- `yaml-config` - YAML configuration file parser
- `ini-reader` - Simple INI file reader and writer
- `csv-parser` - High-performance CSV file parser

### Utilities
- `logger` - Thread-safe logging library
- `string-utils` - String manipulation utilities
- `datetime-utils` - Date and time utilities
- `timer` - High-resolution timer library
- `uuid-generator` - UUID generation library
- `cli-parser` - Command-line argument parser

### Cryptography & Security
- `crypto-utils` - Cryptographic utilities library
- `hash-functions` - Collection of hash functions
- `encryption` - Encryption and decryption utilities
- `jwt-auth` - JSON Web Token library
- `oauth-client` - OAuth 2.0 client library

### Math & Science
- `math-lib` - Mathematical functions library
- `vector-math` - Vector and matrix operations
- `geometry` - Geometric calculations library
- `statistics` - Statistical analysis functions
- `random-gen` - Random number generators

### Data Structures & Algorithms
- `queue` - Thread-safe queue implementations
- `stack` - Stack data structure utilities
- `tree` - Tree data structure library
- `graph` - Graph algorithms library
- `sorting` - Sorting algorithms collection
- `searching` - Search algorithms library

### Networking
- `network-lib` - Network communication library
- `http-client` - HTTP client library
- `websocket` - WebSocket implementation
- `tcp-server` - TCP server framework
- `udp-socket` - UDP socket wrapper

### Concurrency
- `threading` - Threading utilities and primitives
- `async-io` - Asynchronous I/O operations

### Storage & Caching
- `database-connector` - Database connection library
- `cache-manager` - In-memory cache management
- `serialization` - Object serialization library
- `compression` - Data compression algorithms

### Media & Documents
- `image-proc` - Image processing library
- `audio-codec` - Audio codec library
- `video-decoder` - Video decoding utilities
- `pdf-generator` - PDF generation library
- `barcode-reader` - Barcode reading library
- `qr-code` - QR code generation and reading

### Text Processing
- `regex` - Regular expression library
- `template-engine` - Text template engine
- `markdown-parser` - Markdown to HTML converter
- `html-sanitizer` - HTML sanitization library
- `url-parser` - URL parsing and manipulation
- `email-validator` - Email address validation

## 🎨 Coding Style & Conventions

All packages in this repository follow consistent conventions for predictability and ease of use:

### Naming Conventions

| Element | Convention | Example |
|---------|-----------|---------|
| **Package name** | kebab-case | `json-parser`, `http-client` |
| **Namespace** | snake_case (matches library name) | `json_parser`, `http_client` |
| **Class name** | PascalCase (no underscores) | `JsonParser`, `HttpClient` |
| **Library file** | snake_case | `json_parser`, `http_client` |

### Uniform API Pattern

All wrapper packages provide a consistent interface:

```cpp
#include <package_name.h>

namespace package_name {

class PackageName {
public:
    PackageName();
    ~PackageName();
    
    void initialize();  // Setup/initialization
    bool process();     // Main functionality
    
private:
    class Impl;         // Pimpl pattern for implementation hiding
    Impl* pImpl;
};

} // namespace package_name
```

### Example Usage

```cpp
// json-parser package
#include <json_parser.h>

json_parser::JsonParser parser;
parser.initialize();
bool success = parser.process();
```

```cpp
// logger package
#include <logger.h>

logger::Logger log;
log.initialize();
log.process();
```

### C++ Standards

- **C++17** - Minimum required standard
- **Modern CMake** - 3.15 or higher
- **Pimpl Pattern** - Used for implementation hiding when wrapping real libraries
- **Header Guards** - Traditional `#ifndef` style (not `#pragma once`)

### CMake Conventions

```cmake
# Project naming matches package name
project(package-name CXX)

# Library target uses snake_case
add_library(package_name src/package_name.cpp)

# Public headers in include/
target_include_directories(package_name PUBLIC
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
    $<INSTALL_INTERFACE:include>
)
```

### Why This Matters

- ✅ **Predictable**: Once you learn one package, you know them all
- ✅ **Maintainable**: Consistent structure makes maintenance easier
- ✅ **Professional**: Follows industry best practices
- ✅ **Extensible**: Easy to add new packages following the same pattern

## 🚀 Quick Start

### Prerequisites

- Python 3.7 or higher
- Conan 2.x (`pip install conan`)
- CMake 3.15 or higher
- A C++17 compatible compiler

### Install Conan

```bash
pip install conan
```

### Add This Repository as a Conan Remote

```bash
# For local development, you can add the recipes directory
conan remote add diy-conan-center https://github.com/johndoe6345789/diyconancenter.git
```

### Using Packages

To use a package in your project:

```bash
# Install a package
conan install --requires=json-parser/1.0.0

# Or add to your conanfile.txt
[requires]
json-parser/1.0.0
logger/2.0.0
http-client/2.2.0

# Or in your conanfile.py
def requirements(self):
    self.requires("json-parser/1.0.0")
    self.requires("logger/2.0.0")
```

## 🏗️ Repository Structure

```
diyconancenter/
├── recipes/                         # All package recipes
│   ├── json-parser/
│   │   ├── config.yml              # Version mapping
│   │   └── all/                    # Recipe implementation
│   │       ├── conanfile.py        # Main recipe file
│   │       ├── conandata.yml       # Source URLs and checksums
│   │       ├── CMakeLists.txt      # Build configuration
│   │       ├── src/                # Source files
│   │       ├── include/            # Header files
│   │       └── test_package/       # Package tests
│   └── [49 more packages...]
├── tla-specs/                      # TLA+ formal specifications
│   ├── UniformWrapperPattern.tla   # Pimpl pattern spec
│   ├── ComponentBasedArchitecture.tla  # Game dev pattern spec
│   ├── MiddlewareChainPattern.tla  # Web pattern spec
│   ├── ResourceManagementPattern.tla   # Resource handling spec
│   ├── PluginArchitecturePattern.tla   # Plugin system spec
│   ├── AsyncIOPattern.tla          # Async I/O spec
│   └── README.md                   # TLA+ documentation
├── docs/                           # GitHub Pages documentation
│   ├── index.html                  # Package index page
│   └── packages.json               # Package metadata
├── scripts/                        # Utility scripts
│   ├── generate_packages.py        # Package generator
│   ├── generate_index.py           # Index page generator
│   ├── validate_design_patterns.py # Design pattern validator
│   └── pre-commit-hook.sh          # Pre-commit validation
├── .design-patterns.yml            # Validation configuration
├── ARCHITECTURAL_PATTERNS.md       # Design pattern documentation
├── DESIGN_PATTERN_ENFORCEMENT.md   # Tooling documentation
└── .github/
    └── workflows/
        └── build-packages.yml      # CI/CD pipeline with validation
```

## 🔧 Development

### Design Pattern Validation

All packages must follow architectural design patterns. Validation runs automatically:

**Local validation:**
```bash
# Check your package follows patterns
python3 scripts/validate_design_patterns.py

# Install pre-commit hook (recommended)
ln -s ../../scripts/pre-commit-hook.sh .git/hooks/pre-commit
```

**Automatic validation:**
- ✅ Runs on every push and PR
- ✅ Blocks merging if errors found
- ✅ See [DESIGN_PATTERN_ENFORCEMENT.md](DESIGN_PATTERN_ENFORCEMENT.md)

**Design patterns by domain:**
- See [ARCHITECTURAL_PATTERNS.md](ARCHITECTURAL_PATTERNS.md) for patterns covering:
  - Game development (physics, graphics, audio)
  - Web development (HTTP, WebSocket, REST)
  - CAD/3D printing (geometry, slicing, G-code)
  - AI/ML (inference, computer vision, NLP)
  - Dev tools (analyzers, formatters, profilers)
  - Server tools (containers, networking, monitoring)

**Formal verification with TLA+:**
- See [tla-specs/README.md](tla-specs/README.md) for formal specifications
- All major patterns have been formally verified using TLA+
- Model checking ensures correctness properties
- Specifications serve as precise documentation

### Creating a New Package

1. Create a new directory under `recipes/`:
```bash
mkdir -p recipes/my-package/all
```

2. Create the required files:
   - `config.yml` - Version configuration
   - `all/conanfile.py` - Recipe implementation
   - `all/conandata.yml` - Source information
   - `all/test_package/` - Test package

3. Use the existing packages as templates!

### Generate Package Index

```bash
python3 scripts/generate_index.py
```

This will update the `docs/index.html` with all available packages.

### Testing Packages Locally

```bash
cd recipes/json-parser/all
conan create . --build=missing
```

## 🤖 GitHub Actions

This repository uses GitHub Actions for:

1. **Building Packages** - Automatically builds all packages on push
   - Tests on Ubuntu, Windows, and macOS
   - Validates package structure
   - Runs test packages

2. **Publishing Documentation** - Generates and deploys the package index to GitHub Pages
   - Creates searchable package list
   - Updates on every push to main

### Workflow Status

[![Build Conan Packages](https://github.com/johndoe6345789/diyconancenter/workflows/Build%20Conan%20Packages/badge.svg)](https://github.com/johndoe6345789/diyconancenter/actions)

## 📖 Documentation

- [Conan Documentation](https://docs.conan.io/)
- [Creating Conan Packages](https://docs.conan.io/2/tutorial/creating_packages.html)
- [Conan Center Index](https://github.com/conan-io/conan-center-index)

## 🤝 Contributing

This is a demonstration repository, but you can:

1. Fork this repository
2. Add your own packages
3. Customize the workflow
4. Deploy your own DIY Conan Center!

## 📝 License

MIT License - See [LICENSE](LICENSE) file for details.

## 🙏 Acknowledgments

- Inspired by [Conan Center Index](https://github.com/conan-io/conan-center-index)
- Built with [Conan](https://conan.io/)
- Powered by [GitHub Actions](https://github.com/features/actions)
- Hosted on [GitHub Pages](https://pages.github.com/)

## 📧 Contact

For questions or suggestions, please open an issue on GitHub.

---

**Made with ❤️ for the C/C++ community**