from conan import ConanFile


class LoggerConan(ConanFile):
    name = "logger"
    version = "1.13.0"
    description = "Wrapper for spdlog from Conan Center"
    license = "MIT"
    author = "DIY Conan Center"
    url = "https://github.com/gabime/spdlog"
    topics = ("c++", "library", "logger", "spdlog")
    
    def requirements(self):
        # Pull the actual library from Conan Center
        self.requires("spdlog/1.13.0")
    
    def package_id(self):
        # This is a header-only wrapper, so it doesn't depend on settings
        self.info.clear()
    
    def package_info(self):
        # Propagate the dependency information
        self.cpp_info.bindirs = []
        self.cpp_info.libdirs = []
