#!/usr/bin/env python3
"""
Design Pattern Validator for DIY Conan Center packages.
Validates that packages follow architectural design patterns and conventions.
"""

import os
import sys
import re
from pathlib import Path
from typing import List, Dict, Tuple, Optional
import yaml


class ValidationError:
    """Represents a validation error."""
    def __init__(self, severity: str, package: str, rule: str, message: str, file: str = ""):
        self.severity = severity  # "error", "warning", "info"
        self.package = package
        self.rule = rule
        self.message = message
        self.file = file
    
    def __str__(self):
        loc = f" in {self.file}" if self.file else ""
        return f"[{self.severity.upper()}] {self.package}{loc}: {self.rule} - {self.message}"


class DesignPatternValidator:
    """Validates packages against design patterns."""
    
    def __init__(self, repo_root: Path):
        self.repo_root = repo_root
        self.recipes_dir = repo_root / "recipes"
        self.errors: List[ValidationError] = []
        
    def validate_all_packages(self) -> List[ValidationError]:
        """Validate all packages in the repository."""
        if not self.recipes_dir.exists():
            self.errors.append(ValidationError(
                "error", "repository", "structure",
                f"Recipes directory not found: {self.recipes_dir}"
            ))
            return self.errors
        
        packages = [p for p in self.recipes_dir.iterdir() if p.is_dir()]
        print(f"Found {len(packages)} packages to validate")
        
        for package_dir in packages:
            package_name = package_dir.name
            print(f"Validating {package_name}...")
            self.validate_package(package_name, package_dir)
        
        return self.errors
    
    def validate_package(self, package_name: str, package_dir: Path):
        """Validate a single package."""
        # Find the version directory (usually "all")
        version_dirs = [d for d in package_dir.iterdir() if d.is_dir()]
        if not version_dirs:
            self.errors.append(ValidationError(
                "error", package_name, "structure",
                "No version directory found (expected 'all' or version-specific)"
            ))
            return
        
        version_dir = version_dirs[0]  # Usually "all"
        
        # Run validation checks
        self.check_naming_conventions(package_name)
        self.check_conanfile(package_name, version_dir)
        self.check_directory_structure(package_name, version_dir)
        self.check_header_files(package_name, version_dir)
        self.check_source_files(package_name, version_dir)
        self.check_cmake_files(package_name, version_dir)
        self.check_test_package(package_name, version_dir)
    
    def check_naming_conventions(self, package_name: str):
        """Validate package naming conventions."""
        # Rule: Package names should be kebab-case
        if not re.match(r'^[a-z][a-z0-9]*(-[a-z0-9]+)*$', package_name):
            self.errors.append(ValidationError(
                "error", package_name, "naming",
                f"Package name '{package_name}' should be kebab-case (lowercase with hyphens)"
            ))
        
        # Check for domain prefixes
        domain_prefixes = ['game-', 'web-', 'cad-', 'print-', 'ml-', 'ai-', 'dev-', 'server-']
        has_domain_prefix = any(package_name.startswith(prefix) for prefix in domain_prefixes)
        
        # Warn if package seems domain-specific but lacks prefix
        domain_keywords = {
            'physics', 'graphics', 'audio', 'engine', 'render',  # Game
            'http', 'websocket', 'rest', 'api', 'middleware',  # Web
            'mesh', 'geometry', 'nurbs', 'boolean',  # CAD
            'slice', 'gcode', 'infill', 'support',  # 3D Printing
            'neural', 'inference', 'vision', 'nlp', 'model',  # AI/ML
            'analyzer', 'formatter', 'profiler', 'debugger',  # Dev Tools
            'container', 'kubernetes', 'docker', 'vpn', 'cdn'  # Server
        }
        
        if any(kw in package_name for kw in domain_keywords) and not has_domain_prefix:
            self.errors.append(ValidationError(
                "warning", package_name, "naming",
                f"Domain-specific package should use prefix (e.g., game-, web-, ml-)"
            ))
    
    def check_conanfile(self, package_name: str, version_dir: Path):
        """Validate conanfile.py structure and content."""
        conanfile = version_dir / "conanfile.py"
        if not conanfile.exists():
            self.errors.append(ValidationError(
                "error", package_name, "structure",
                "conanfile.py not found", str(conanfile)
            ))
            return
        
        content = conanfile.read_text()
        
        # Check for required imports
        required_imports = [
            ('from conan import ConanFile', 'ConanFile import'),
        ]
        for import_line, desc in required_imports:
            if import_line not in content:
                self.errors.append(ValidationError(
                    "error", package_name, "conanfile",
                    f"Missing required import: {desc}", str(conanfile)
                ))
        
        # Check for required class attributes
        if 'name = ' not in content:
            self.errors.append(ValidationError(
                "error", package_name, "conanfile",
                "Missing 'name' attribute in ConanFile", str(conanfile)
            ))
        
        if 'version = ' not in content:
            self.errors.append(ValidationError(
                "error", package_name, "conanfile",
                "Missing 'version' attribute in ConanFile", str(conanfile)
            ))
        
        # Check for license
        if 'license = ' not in content:
            self.errors.append(ValidationError(
                "warning", package_name, "conanfile",
                "Missing 'license' attribute", str(conanfile)
            ))
        
        # Check for settings
        if 'settings = ' not in content:
            self.errors.append(ValidationError(
                "warning", package_name, "conanfile",
                "Missing 'settings' attribute", str(conanfile)
            ))
        
        # If uses 'os' module, check it's imported
        if 'os.path' in content or 'os.join' in content:
            if 'import os' not in content:
                self.errors.append(ValidationError(
                    "error", package_name, "conanfile",
                    "Uses 'os' module but doesn't import it", str(conanfile)
                ))
    
    def check_directory_structure(self, package_name: str, version_dir: Path):
        """Validate directory structure."""
        # For packages with source code
        has_src = (version_dir / "src").exists()
        has_include = (version_dir / "include").exists()
        
        if has_src and not has_include:
            self.errors.append(ValidationError(
                "warning", package_name, "structure",
                "Has 'src/' but no 'include/' directory"
            ))
        
        # Check for CMakeLists.txt if there's source
        if has_src:
            cmake_file = version_dir / "CMakeLists.txt"
            if not cmake_file.exists():
                self.errors.append(ValidationError(
                    "error", package_name, "structure",
                    "Has source code but no CMakeLists.txt", str(cmake_file)
                ))
    
    def check_header_files(self, package_name: str, version_dir: Path):
        """Validate header files follow conventions."""
        include_dir = version_dir / "include"
        if not include_dir.exists():
            return
        
        lib_name = package_name.replace("-", "_")
        expected_header = include_dir / f"{lib_name}.h"
        
        header_files = list(include_dir.glob("*.h"))
        if not header_files:
            self.errors.append(ValidationError(
                "warning", package_name, "headers",
                f"No header files found in include/"
            ))
            return
        
        # Check if expected header exists
        if not expected_header.exists():
            self.errors.append(ValidationError(
                "warning", package_name, "headers",
                f"Expected header '{lib_name}.h' not found"
            ))
            return
        
        # Validate header content
        content = expected_header.read_text()
        
        # Check for header guards
        guard_name = f"{lib_name.upper()}_H"
        if f"#ifndef {guard_name}" not in content:
            self.errors.append(ValidationError(
                "warning", package_name, "headers",
                f"Header guard should be '{guard_name}'", str(expected_header)
            ))
        
        # Check for namespace
        if f"namespace {lib_name}" not in content:
            self.errors.append(ValidationError(
                "info", package_name, "headers",
                f"Consider using namespace '{lib_name}'", str(expected_header)
            ))
        
        # Check for Pimpl pattern (if it's a wrapper)
        if "std::unique_ptr<Impl>" in content or "Impl* pImpl" in content:
            # Good - using Pimpl
            if "std::unique_ptr" in content and "Impl* pImpl" in content:
                self.errors.append(ValidationError(
                    "error", package_name, "headers",
                    "Use std::unique_ptr instead of raw pointer for Pimpl",
                    str(expected_header)
                ))
    
    def check_source_files(self, package_name: str, version_dir: Path):
        """Validate source files."""
        src_dir = version_dir / "src"
        if not src_dir.exists():
            return
        
        lib_name = package_name.replace("-", "_")
        expected_source = src_dir / f"{lib_name}.cpp"
        
        if not expected_source.exists():
            self.errors.append(ValidationError(
                "warning", package_name, "source",
                f"Expected source file '{lib_name}.cpp' not found"
            ))
            return
        
        content = expected_source.read_text()
        
        # Check includes corresponding header
        if f'#include "{lib_name}.h"' not in content:
            self.errors.append(ValidationError(
                "warning", package_name, "source",
                f"Should include corresponding header '{lib_name}.h'",
                str(expected_source)
            ))
    
    def check_cmake_files(self, package_name: str, version_dir: Path):
        """Validate CMakeLists.txt."""
        cmake_file = version_dir / "CMakeLists.txt"
        if not cmake_file.exists():
            return
        
        content = cmake_file.read_text()
        lib_name = package_name.replace("-", "_")
        
        # Check minimum CMake version
        if "cmake_minimum_required" not in content:
            self.errors.append(ValidationError(
                "error", package_name, "cmake",
                "Missing cmake_minimum_required", str(cmake_file)
            ))
        
        # Check C++ standard
        if "CMAKE_CXX_STANDARD" not in content:
            self.errors.append(ValidationError(
                "warning", package_name, "cmake",
                "Should specify CMAKE_CXX_STANDARD (17 recommended)", str(cmake_file)
            ))
        
        # Check project name matches package name
        if f"project({package_name}" not in content:
            self.errors.append(ValidationError(
                "warning", package_name, "cmake",
                f"Project name should match package name '{package_name}'", str(cmake_file)
            ))
        
        # Check library target uses snake_case
        if f"add_library({lib_name}" not in content:
            if "add_library(" in content:
                self.errors.append(ValidationError(
                    "warning", package_name, "cmake",
                    f"Library target should be named '{lib_name}'", str(cmake_file)
                ))
    
    def check_test_package(self, package_name: str, version_dir: Path):
        """Validate test_package directory."""
        test_dir = version_dir / "test_package"
        if not test_dir.exists():
            self.errors.append(ValidationError(
                "warning", package_name, "tests",
                "No test_package directory found"
            ))
            return
        
        # Check for test conanfile
        test_conanfile = test_dir / "conanfile.py"
        if not test_conanfile.exists():
            self.errors.append(ValidationError(
                "error", package_name, "tests",
                "test_package/conanfile.py not found", str(test_conanfile)
            ))
        
        # Check for test source
        test_cpp = test_dir / "test_package.cpp"
        if not test_cpp.exists():
            self.errors.append(ValidationError(
                "error", package_name, "tests",
                "test_package/test_package.cpp not found", str(test_cpp)
            ))
        
        # Check for test CMakeLists
        test_cmake = test_dir / "CMakeLists.txt"
        if not test_cmake.exists():
            self.errors.append(ValidationError(
                "error", package_name, "tests",
                "test_package/CMakeLists.txt not found", str(test_cmake)
            ))


def print_summary(errors: List[ValidationError]):
    """Print validation summary."""
    error_count = sum(1 for e in errors if e.severity == "error")
    warning_count = sum(1 for e in errors if e.severity == "warning")
    info_count = sum(1 for e in errors if e.severity == "info")
    
    print("\n" + "=" * 70)
    print("VALIDATION SUMMARY")
    print("=" * 70)
    print(f"Errors:   {error_count}")
    print(f"Warnings: {warning_count}")
    print(f"Info:     {info_count}")
    print("=" * 70)
    
    if errors:
        print("\nIssues found:\n")
        for error in sorted(errors, key=lambda e: (e.severity, e.package)):
            print(f"  {error}")
    else:
        print("\n✅ All packages passed validation!")
    
    print()


def main():
    """Main entry point."""
    repo_root = Path(__file__).parent.parent
    
    print("=" * 70)
    print("DIY CONAN CENTER - DESIGN PATTERN VALIDATOR")
    print("=" * 70)
    print(f"Repository: {repo_root}")
    print()
    
    validator = DesignPatternValidator(repo_root)
    errors = validator.validate_all_packages()
    
    print_summary(errors)
    
    # Exit with error code if there are errors
    error_count = sum(1 for e in errors if e.severity == "error")
    if error_count > 0:
        print(f"❌ Validation failed with {error_count} error(s)")
        return 1
    
    warning_count = sum(1 for e in errors if e.severity == "warning")
    if warning_count > 0:
        print(f"⚠️  Validation passed with {warning_count} warning(s)")
    
    return 0


if __name__ == "__main__":
    sys.exit(main())
