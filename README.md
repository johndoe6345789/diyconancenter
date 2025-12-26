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

Many packages in this repository pull from **real, production-ready open-source libraries** rather than stub implementations. These packages fetch code either from **Conan Center** or directly from upstream **Git repositories**.

### Packages Using Real Libraries from Conan Center

These packages act as wrappers that pull the actual library from Conan Center:

| Package Name | Real Library | Conan Center Package | Upstream Repository |
|--------------|--------------|---------------------|---------------------|
| `json-parser` | nlohmann_json | `nlohmann_json/3.11.3` | [nlohmann/json](https://github.com/nlohmann/json) |
| `xml-parser` | tinyxml2 | `tinyxml2/10.0.0` | [leethomason/tinyxml2](https://github.com/leethomason/tinyxml2) |
| `yaml-config` | yaml-cpp | `yaml-cpp/0.8.0` | [jbeder/yaml-cpp](https://github.com/jbeder/yaml-cpp) |
| `ini-reader` | inih | `inih/58` | [benhoyt/inih](https://github.com/benhoyt/inih) |
| `logger` | spdlog | `spdlog/1.13.0` | [gabime/spdlog](https://github.com/gabime/spdlog) |
| `crypto-utils` | openssl | `openssl/3.2.0` | [openssl/openssl](https://github.com/openssl/openssl) |
| `compression` | zlib | `zlib/1.3.1` | [madler/zlib](https://github.com/madler/zlib) |
| `websocket` | websocketpp | `websocketpp/0.8.2` | [zaphoyd/websocketpp](https://github.com/zaphoyd/websocketpp) |
| `cli-parser` | CLI11 | `cli11/2.4.1` | [CLIUtils/CLI11](https://github.com/CLIUtils/CLI11) |
| `jwt-auth` | jwt-cpp | `jwt-cpp/0.7.0` | [Thalhammer/jwt-cpp](https://github.com/Thalhammer/jwt-cpp) |
| `datetime-utils` | date | `date/3.0.1` | [HowardHinnant/date](https://github.com/HowardHinnant/date) |
| `regex` | re2 | `re2/2023-11-01` | [google/re2](https://github.com/google/re2) |

### Packages Fetching Source Directly from Git

These packages download source code directly from upstream repositories:

| Package Name | Real Library | Version | Upstream Repository |
|--------------|--------------|---------|---------------------|
| `csv-parser` | csv-parser | 2.3.0 | [vincentlaucsb/csv-parser](https://github.com/vincentlaucsb/csv-parser) |
| `http-client` | cpp-httplib | 0.15.3 | [yhirose/cpp-httplib](https://github.com/yhirose/cpp-httplib) |
| `hash-functions` | hash-library | 8 | [stbrumme/hash-library](https://github.com/stbrumme/hash-library) |

### DIY/Stub Implementations

The remaining packages (~35) are simple DIY implementations useful for demonstration and testing purposes.

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
├── recipes/                    # All package recipes
│   ├── json-parser/
│   │   ├── config.yml         # Version mapping
│   │   └── all/               # Recipe implementation
│   │       ├── conanfile.py   # Main recipe file
│   │       ├── conandata.yml  # Source URLs and checksums
│   │       ├── CMakeLists.txt # Build configuration
│   │       ├── src/           # Source files
│   │       ├── include/       # Header files
│   │       └── test_package/  # Package tests
│   └── [49 more packages...]
├── docs/                      # GitHub Pages documentation
│   ├── index.html            # Package index page
│   └── packages.json         # Package metadata
├── scripts/                  # Utility scripts
│   ├── generate_packages.py # Package generator
│   └── generate_index.py    # Index page generator
└── .github/
    └── workflows/
        └── build-packages.yml # CI/CD pipeline
```

## 🔧 Development

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