# DIY Conan Center Documentation

## Overview

This repository demonstrates how to create a self-hosted Conan package repository with automated building and a beautiful web interface hosted on GitHub Pages.

## Architecture

### Components

1. **Recipe Repository** (`recipes/`)
   - Contains all Conan package recipes
   - Each package has its own directory
   - Follows Conan Center Index conventions
   - **Features real library integration**: Many packages pull from actual open-source libraries

2. **GitHub Actions** (`.github/workflows/`)
   - Automatically builds packages on push
   - Tests packages on multiple platforms
   - Generates and publishes documentation

3. **GitHub Pages** (`docs/`)
   - Hosts the package index
   - Provides searchable interface
   - Auto-generated from recipes

## Real Library Integration

This repository demonstrates **two approaches** for providing packages:

### 1. Conan Center Wrappers

These packages act as wrappers that fetch dependencies from Conan Center. This approach:
- Leverages existing, well-tested packages
- Provides familiar names for common libraries
- Requires minimal maintenance
- Automatically gets updates when Conan Center packages are updated

**Example packages:**
- `json-parser` → wraps `nlohmann_json/3.11.3`
- `logger` → wraps `spdlog/1.13.0`
- `crypto-utils` → wraps `openssl/3.2.0`

**Recipe structure:**
```python
class JsonparserConan(ConanFile):
    name = "json-parser"
    version = "3.11.3"
    
    def requirements(self):
        # Pull the actual library from Conan Center
        self.requires("nlohmann_json/3.11.3")
```

### 2. Git Source Fetching

These packages download source code directly from upstream repositories. This approach:
- Provides access to libraries not yet in Conan Center
- Allows customization of build configuration
- Enables packaging of niche or specialized libraries
- Gives full control over the build process

**Example packages:**
- `csv-parser` → fetches from [vincentlaucsb/csv-parser](https://github.com/vincentlaucsb/csv-parser)
- `http-client` → fetches from [yhirose/cpp-httplib](https://github.com/yhirose/cpp-httplib)

**Recipe structure:**
```python
class CsvparserConan(ConanFile):
    name = "csv-parser"
    version = "2.3.0"
    
    def source(self):
        # Download and extract from upstream
        get(self, **self.conan_data["sources"][self.version], 
            destination=self.source_folder, strip_root=True)
    
    def build(self):
        cmake = CMake(self)
        cmake.configure()
        cmake.build()
```

### 3. DIY Implementations

Simple packages remain as demonstration/stub implementations useful for:
- Teaching Conan package creation
- Testing infrastructure
- Placeholder implementations

**Current Status:**
- 19 packages pull from real libraries (13 from Conan Center, 6 from Git)
- 2 packages have uniform wrapper APIs (json-parser, logger)
- 31 packages are DIY/stub implementations

**Note on SHA256 Checksums:**
Some packages that fetch from Git currently use placeholder SHA256 values. In production use, these should be replaced with actual checksums calculated from the downloaded archives. This is a known limitation for demonstration purposes. To generate real checksums:
```bash
curl -L <archive-url> | sha256sum
```

### Package Structure

Each package follows this structure:

```
recipes/
└── package-name/
    ├── config.yml              # Maps versions to folders
    └── all/                    # Can be version-specific too
        ├── conanfile.py        # Main recipe
        ├── conandata.yml       # Source URLs and checksums
        ├── CMakeLists.txt      # Build configuration
        ├── src/                # Source files
        ├── include/            # Header files
        └── test_package/       # Validation tests
            ├── conanfile.py
            ├── CMakeLists.txt
            └── test_package.cpp
```

## Workflows

### Build Workflow

The `build-packages.yml` workflow:

1. **Triggers on:**
   - Push to main/master
   - Pull requests
   - Manual dispatch

2. **Build Matrix:**
   - Ubuntu (Linux)
   - Windows
   - macOS

3. **Steps:**
   - Checkout code
   - Setup Python and Conan
   - Detect Conan profile
   - Build all packages
   - Generate index page
   - Deploy to GitHub Pages

### Index Generation

The `generate_index.py` script:

1. Scans all recipes
2. Extracts package metadata
3. Generates HTML index
4. Creates JSON manifest
5. Outputs to docs/ directory

## Using Packages

### Method 1: Conanfile.txt

```ini
[requires]
json-parser/1.0.0
logger/2.0.0

[generators]
CMakeDeps
CMakeToolchain
```

### Method 2: Conanfile.py

```python
from conan import ConanFile

class MyProjectConan(ConanFile):
    settings = "os", "compiler", "build_type", "arch"
    generators = "CMakeDeps", "CMakeToolchain"
    
    def requirements(self):
        self.requires("json-parser/1.0.0")
        self.requires("logger/2.0.0")
```

### Method 3: Command Line

```bash
conan install --requires=json-parser/1.0.0 --build=missing
```

## Creating New Packages

### Step 1: Create Directory Structure

```bash
mkdir -p recipes/my-package/all/{src,include,test_package}
```

### Step 2: Create config.yml

```yaml
versions:
  "1.0.0":
    folder: all
```

### Step 3: Create conanfile.py

```python
from conan import ConanFile
from conan.tools.cmake import CMakeToolchain, CMake, cmake_layout

class MyPackageConan(ConanFile):
    name = "my-package"
    version = "1.0.0"
    description = "My awesome package"
    license = "MIT"
    settings = "os", "compiler", "build_type", "arch"
    options = {"shared": [True, False]}
    default_options = {"shared": False}
    exports_sources = "CMakeLists.txt", "src/*", "include/*"
    
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
        self.cpp_info.libs = ["my_package"]
```

### Step 4: Create conandata.yml

```yaml
sources:
  "1.0.0":
    url: "https://github.com/example/my-package/archive/v1.0.0.tar.gz"
    sha256: "your-sha256-checksum-here"
```

### Step 5: Create CMakeLists.txt

```cmake
cmake_minimum_required(VERSION 3.15)
project(my-package CXX)

set(CMAKE_CXX_STANDARD 17)

add_library(my_package src/my_package.cpp)
target_include_directories(my_package PUBLIC
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
    $<INSTALL_INTERFACE:include>
)

install(TARGETS my_package
    ARCHIVE DESTINATION lib
    LIBRARY DESTINATION lib
    RUNTIME DESTINATION bin
)
install(DIRECTORY include/ DESTINATION include)
```

### Step 6: Create Test Package

Create `test_package/conanfile.py`:

```python
from conan import ConanFile
from conan.tools.cmake import CMake, cmake_layout
from conan.tools.build import can_run

class MyPackageTestConan(ConanFile):
    settings = "os", "compiler", "build_type", "arch"
    generators = "CMakeDeps", "CMakeToolchain"

    def requirements(self):
        self.requires(self.tested_reference_str)

    def build(self):
        cmake = CMake(self)
        cmake.configure()
        cmake.build()

    def test(self):
        if can_run(self):
            self.run(os.path.join(self.cpp.build.bindir, "test_package"))
```

### Step 7: Test Locally

```bash
cd recipes/my-package/all
conan create . --build=missing
```

### Step 8: Commit and Push

```bash
git add recipes/my-package
git commit -m "Add my-package"
git push
```

GitHub Actions will automatically:
- Build the package
- Test it on multiple platforms
- Update the package index
- Deploy to GitHub Pages

## Best Practices

### 1. Using Real Libraries

**When to use Conan Center wrappers:**
- Library already exists in Conan Center
- You want stable, tested packages
- Minimal customization needed

**When to fetch from Git:**
- Library not yet in Conan Center
- Need specific build configuration
- Want to track upstream closely

**Adding new real library mappings:**

1. Edit `scripts/real_libraries_mapping.py`
2. Add entry to `REAL_LIBRARIES` dictionary:

```python
"my-package": {
    "upstream_url": "https://github.com/author/repo",
    "real_name": "real-library-name",
    "version": "1.2.3",
    "archive_url": "https://github.com/author/repo/archive/v1.2.3.tar.gz",
    "sha256": "actual-sha256-checksum",
    "use_conan_center": True,  # or False
    "conan_center_name": "package-name",  # if use_conan_center
},
```

3. Run the update script:
```bash
python3 scripts/update_to_real_libraries.py
```

4. Test the updated package:
```bash
cd recipes/my-package/all
conan create . --build=missing
```

### 2. Version Management

- Use semantic versioning (MAJOR.MINOR.PATCH)
- Keep different versions in separate folders if they differ significantly
- Use `all/` folder for recipes that work across versions

### 2. Dependencies

- Declare all dependencies in `requirements()`
- Use version ranges carefully
- Test with `--build=missing`

### 3. Cross-Platform Support

- Test on Linux, Windows, and macOS
- Handle platform-specific code properly
- Use Conan settings and options

### 4. Documentation

- Add clear descriptions to packages
- Document options and settings
- Provide usage examples

### 5. Testing

- Always include a test_package
- Test both static and shared builds
- Verify the package works as expected

## Troubleshooting

### Package Build Fails

1. Check CMakeLists.txt syntax
2. Verify source file paths
3. Check compiler requirements
4. Review dependencies

### Test Package Fails

1. Verify library linking
2. Check include paths
3. Ensure all dependencies are found
4. Review test code

### GitHub Actions Fails

1. Check workflow logs
2. Verify Python/Conan versions
3. Check recipe syntax
4. Test locally first

## Advanced Topics

### Custom Remotes

To use this repository as a remote:

```bash
# Add remote
conan remote add mydiy https://raw.githubusercontent.com/johndoe6345789/diyconancenter/main

# List remotes
conan remote list

# Search packages
conan search "*" -r=mydiy
```

### Binary Packages

To build and upload binary packages:

```bash
# Build package
conan create recipes/my-package/all --build=missing

# Upload to remote (requires authentication)
conan upload my-package/1.0.0 -r=mydiy --all
```

### Custom Profiles

Create custom build profiles:

```bash
# Create profile
conan profile detect --force

# Edit profile
conan profile path default

# Use custom profile
conan create . --profile=myprofile
```

## Resources

- [Conan Documentation](https://docs.conan.io/)
- [Conan Center Index](https://github.com/conan-io/conan-center-index)
- [CMake Documentation](https://cmake.org/documentation/)
- [GitHub Actions](https://docs.github.com/en/actions)

## Support

For issues or questions:

1. Check the documentation
2. Review existing packages as examples
3. Open an issue on GitHub
4. Consult Conan documentation

---

Last updated: 2025-12-26
