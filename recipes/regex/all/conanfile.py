from conan import ConanFile


class RegexConan(ConanFile):
    name = "regex"
    version = "2023-11-01"
    description = "Wrapper for re2 from Conan Center"
    license = "MIT"
    author = "DIY Conan Center"
    url = "https://github.com/google/re2"
    topics = ("c++", "library", "regex", "re2")
    
    def requirements(self):
        # Pull the actual library from Conan Center
        self.requires("re2/2023-11-01")
    
    def package_id(self):
        # This is a header-only wrapper, so it doesn't depend on settings
        self.info.clear()
    
    def package_info(self):
        # Propagate the dependency information
        self.cpp_info.bindirs = []
        self.cpp_info.libdirs = []
