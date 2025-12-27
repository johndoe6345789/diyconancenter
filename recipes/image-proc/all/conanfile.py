from conan import ConanFile


class ImageprocConan(ConanFile):
    name = "image-proc"
    version = "master"
    description = "Wrapper for stb from Conan Center"
    license = "MIT"
    author = "DIY Conan Center"
    url = "https://github.com/nothings/stb"
    topics = ("c++", "library", "image-proc", "stb")
    
    def requirements(self):
        # Pull the actual library from Conan Center
        self.requires("stb/master")
    
    def package_id(self):
        # This is a header-only wrapper, so it doesn't depend on settings
        self.info.clear()
    
    def package_info(self):
        # Propagate the dependency information
        self.cpp_info.bindirs = []
        self.cpp_info.libdirs = []
