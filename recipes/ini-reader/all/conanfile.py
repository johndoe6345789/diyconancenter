from conan import ConanFile


class InireaderConan(ConanFile):
    name = "ini-reader"
    version = "58"
    description = "Wrapper for inih from Conan Center"
    license = "MIT"
    author = "DIY Conan Center"
    url = "https://github.com/benhoyt/inih"
    topics = ("c++", "library", "ini-reader", "inih")
    
    def requirements(self):
        # Pull the actual library from Conan Center
        self.requires("inih/58")
    
    def package_id(self):
        # This is a header-only wrapper, so it doesn't depend on settings
        self.info.clear()
    
    def package_info(self):
        # Propagate the dependency information
        self.cpp_info.bindirs = []
        self.cpp_info.libdirs = []
