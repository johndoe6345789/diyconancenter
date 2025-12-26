from conan import ConanFile


class JsonparserConan(ConanFile):
    name = "json-parser"
    version = "3.11.3"
    description = "Wrapper for nlohmann_json from Conan Center"
    license = "MIT"
    author = "DIY Conan Center"
    url = "https://github.com/nlohmann/json"
    topics = ("c++", "library", "json-parser", "nlohmann_json")
    
    def requirements(self):
        # Pull the actual library from Conan Center
        self.requires("nlohmann_json/3.11.3")
    
    def package_id(self):
        # This is a header-only wrapper, so it doesn't depend on settings
        self.info.clear()
    
    def package_info(self):
        # Propagate the dependency information
        self.cpp_info.bindirs = []
        self.cpp_info.libdirs = []
