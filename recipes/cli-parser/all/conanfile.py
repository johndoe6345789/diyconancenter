from conan import ConanFile


class CliparserConan(ConanFile):
    name = "cli-parser"
    version = "2.4.1"
    description = "Wrapper for cli11 from Conan Center"
    license = "MIT"
    author = "DIY Conan Center"
    url = "https://github.com/CLIUtils/CLI11"
    topics = ("c++", "library", "cli-parser", "CLI11")
    
    def requirements(self):
        # Pull the actual library from Conan Center
        self.requires("cli11/2.4.1")
    
    def package_id(self):
        # This is a header-only wrapper, so it doesn't depend on settings
        self.info.clear()
    
    def package_info(self):
        # Propagate the dependency information
        self.cpp_info.bindirs = []
        self.cpp_info.libdirs = []
