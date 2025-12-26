#!/usr/bin/env python3
"""
Update DIY packages to pull from real upstream libraries.
This script modifies conanfile.py and conandata.yml to use real source code.
"""

import os
import sys
from pathlib import Path
import yaml

# Add the scripts directory to the path to import our mapping
sys.path.insert(0, str(Path(__file__).parent))
from real_libraries_mapping import get_library_info, get_all_real_packages


def create_conanfile_with_source(package_name, info):
    """Create a conanfile.py that fetches from upstream source."""
    class_name = package_name.replace("-", "").title()
    lib_name = package_name.replace("-", "_")
    
    return f'''from conan import ConanFile
from conan.tools.cmake import CMakeToolchain, CMake, cmake_layout, CMakeDeps
from conan.tools.files import get, copy
import os


class {class_name}Conan(ConanFile):
    name = "{package_name}"
    version = "{info['version']}"
    description = "Real {info['real_name']} library - {package_name}"
    license = "MIT"
    author = "DIY Conan Center"
    url = "{info['upstream_url']}"
    topics = ("c++", "library", "{package_name}", "{info['real_name']}")
    settings = "os", "compiler", "build_type", "arch"
    options = {{"shared": [True, False], "fPIC": [True, False]}}
    default_options = {{"shared": False, "fPIC": True}}
    
    def config_options(self):
        if self.settings.os == "Windows":
            del self.options.fPIC
    
    def configure(self):
        if self.options.shared:
            self.options.rm_safe("fPIC")
    
    def source(self):
        # Download and extract the source code from upstream
        get(self, **self.conan_data["sources"][self.version], 
            destination=self.source_folder, strip_root=True)
    
    def layout(self):
        cmake_layout(self, src_folder="src")
    
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
        # Copy license files
        copy(self, "LICENSE*", src=self.source_folder, dst=os.path.join(self.package_folder, "licenses"))
    
    def package_info(self):
        self.cpp_info.libs = ["{lib_name}"]
'''


def create_conandata_with_real_source(info):
    """Create conandata.yml with real upstream source information."""
    return {
        "sources": {
            info['version']: {
                "url": info['archive_url'],
                "sha256": info['sha256']
            }
        }
    }


def create_conanfile_as_requirement(package_name, info):
    """
    Create a conanfile.py that just requires the package from Conan Center.
    This is for packages that exist in Conan Center and we want to use them directly.
    """
    class_name = package_name.replace("-", "").title()
    
    return f'''from conan import ConanFile


class {class_name}Conan(ConanFile):
    name = "{package_name}"
    version = "{info['version']}"
    description = "Wrapper for {info['conan_center_name']} from Conan Center"
    license = "MIT"
    author = "DIY Conan Center"
    url = "{info['upstream_url']}"
    topics = ("c++", "library", "{package_name}", "{info['real_name']}")
    
    def requirements(self):
        # Pull the actual library from Conan Center
        self.requires("{info['conan_center_name']}/{info['version']}")
    
    def package_id(self):
        # This is a header-only wrapper, so it doesn't depend on settings
        self.info.clear()
    
    def package_info(self):
        # Propagate the dependency information
        self.cpp_info.bindirs = []
        self.cpp_info.libdirs = []
'''


def update_package(base_path, package_name, info):
    """Update a single package to use real library source."""
    package_path = base_path / package_name / "all"
    
    if not package_path.exists():
        print(f"Warning: Package path {package_path} does not exist, skipping...")
        return False
    
    print(f"Updating {package_name} to use {info['real_name']} from {info['upstream_url']}...")
    
    if info.get('use_conan_center', False):
        # For packages in Conan Center, create a wrapper that requires them
        print(f"  -> Creating Conan Center wrapper for {info['conan_center_name']}")
        conanfile_content = create_conanfile_as_requirement(package_name, info)
        
        # Write the new conanfile.py
        with open(package_path / "conanfile.py", "w") as f:
            f.write(conanfile_content)
        
        # Update conandata.yml with upstream source info (for reference)
        conandata = create_conandata_with_real_source(info)
        with open(package_path / "conandata.yml", "w") as f:
            yaml.dump(conandata, f, default_flow_style=False, sort_keys=False)
        
        # Remove src and include directories as they're not needed
        import shutil
        src_dir = package_path / "src"
        include_dir = package_path / "include"
        if src_dir.exists():
            shutil.rmtree(src_dir)
        if include_dir.exists():
            shutil.rmtree(include_dir)
        
    else:
        # For packages not in Conan Center, create a recipe that fetches source
        print(f"  -> Creating source-fetching recipe")
        conanfile_content = create_conanfile_with_source(package_name, info)
        
        # Write the new conanfile.py
        with open(package_path / "conanfile.py", "w") as f:
            f.write(conanfile_content)
        
        # Update conandata.yml with real source URLs
        conandata = create_conandata_with_real_source(info)
        with open(package_path / "conandata.yml", "w") as f:
            yaml.dump(conandata, f, default_flow_style=False, sort_keys=False)
    
    print(f"  ✓ Successfully updated {package_name}")
    return True


def main():
    """Main function."""
    repo_root = Path(__file__).parent.parent
    recipes_dir = repo_root / "recipes"
    
    if not recipes_dir.exists():
        print(f"Error: Recipes directory {recipes_dir} not found!")
        return 1
    
    print("=" * 70)
    print("Updating DIY Conan packages to use real upstream libraries")
    print("=" * 70)
    print()
    
    real_packages = get_all_real_packages()
    print(f"Found {len(real_packages)} packages with real library mappings")
    print()
    
    updated = 0
    skipped = 0
    
    for package_name in real_packages:
        info = get_library_info(package_name)
        if info:
            if update_package(recipes_dir, package_name, info):
                updated += 1
            else:
                skipped += 1
        print()
    
    print("=" * 70)
    print(f"Summary: Updated {updated} packages, Skipped {skipped} packages")
    print("=" * 70)
    print()
    print("Packages updated to pull from real libraries:")
    for package_name in real_packages:
        info = get_library_info(package_name)
        if info:
            source = f"Conan Center ({info['conan_center_name']})" if info.get('use_conan_center') else "Git source"
            print(f"  - {package_name:20} -> {info['real_name']:20} [{source}]")
    
    return 0


if __name__ == "__main__":
    sys.exit(main())
