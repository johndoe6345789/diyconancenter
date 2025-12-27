from conan import ConanFile


class CryptoutilsConan(ConanFile):
    name = "crypto-utils"
    version = "3.2.0"
    description = "Wrapper for openssl from Conan Center"
    license = "MIT"
    author = "DIY Conan Center"
    url = "https://github.com/openssl/openssl"
    topics = ("c++", "library", "crypto-utils", "openssl")
    
    def requirements(self):
        # Pull the actual library from Conan Center
        self.requires("openssl/3.2.0")
    
    def package_id(self):
        # This is a header-only wrapper, so it doesn't depend on settings
        self.info.clear()
    
    def package_info(self):
        # Propagate the dependency information
        self.cpp_info.bindirs = []
        self.cpp_info.libdirs = []
