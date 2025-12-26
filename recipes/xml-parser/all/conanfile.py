from conan import ConanFile


class XmlparserConan(ConanFile):
    name = "xml-parser"
    version = "10.0.0"
    description = "Wrapper for tinyxml2 from Conan Center"
    license = "MIT"
    author = "DIY Conan Center"
    url = "https://github.com/leethomason/tinyxml2"
    topics = ("c++", "library", "xml-parser", "tinyxml2")
    
    def requirements(self):
        # Pull the actual library from Conan Center
        self.requires("tinyxml2/10.0.0")
    
    def package_id(self):
        # This is a header-only wrapper, so it doesn't depend on settings
        self.info.clear()
    
    def package_info(self):
        # Propagate the dependency information
        self.cpp_info.bindirs = []
        self.cpp_info.libdirs = []
