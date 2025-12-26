# DIY Conan Center Documentation

## Overview

This repository demonstrates how to create a self-hosted Conan package repository with automated building and a beautiful web interface hosted on GitHub Pages.

## Architecture

### Components

1. **Recipe Repository** (`recipes/`)
   - Contains all Conan package recipes
   - Each package has its own directory
   - Follows Conan Center Index conventions

2. **GitHub Actions** (`.github/workflows/`)
   - Automatically builds packages on push
   - Tests packages on multiple platforms
   - Generates and publishes documentation

3. **GitHub Pages** (`docs/`)
   - Hosts the package index
   - Provides searchable interface
   - Auto-generated from recipes

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

### 1. Version Management

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
