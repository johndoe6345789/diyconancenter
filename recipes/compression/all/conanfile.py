from conan import ConanFile


class CompressionConan(ConanFile):
    name = "compression"
    version = "1.3.1"
    description = "Wrapper for zlib from Conan Center"
    license = "MIT"
    author = "DIY Conan Center"
    url = "https://github.com/madler/zlib"
    topics = ("c++", "library", "compression", "zlib")
    
    def requirements(self):
        # Pull the actual library from Conan Center
        self.requires("zlib/1.3.1")
    
    def package_id(self):
        # This is a header-only wrapper, so it doesn't depend on settings
        self.info.clear()
    
    def package_info(self):
        # Propagate the dependency information
        self.cpp_info.bindirs = []
        self.cpp_info.libdirs = []
