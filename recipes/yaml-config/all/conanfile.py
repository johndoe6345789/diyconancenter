from conan import ConanFile


class YamlconfigConan(ConanFile):
    name = "yaml-config"
    version = "0.8.0"
    description = "Wrapper for yaml-cpp from Conan Center"
    license = "MIT"
    author = "DIY Conan Center"
    url = "https://github.com/jbeder/yaml-cpp"
    topics = ("c++", "library", "yaml-config", "yaml-cpp")
    
    def requirements(self):
        # Pull the actual library from Conan Center
        self.requires("yaml-cpp/0.8.0")
    
    def package_id(self):
        # This is a header-only wrapper, so it doesn't depend on settings
        self.info.clear()
    
    def package_info(self):
        # Propagate the dependency information
        self.cpp_info.bindirs = []
        self.cpp_info.libdirs = []
