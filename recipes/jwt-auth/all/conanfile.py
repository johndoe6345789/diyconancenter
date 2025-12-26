from conan import ConanFile


class JwtauthConan(ConanFile):
    name = "jwt-auth"
    version = "0.7.0"
    description = "Wrapper for jwt-cpp from Conan Center"
    license = "MIT"
    author = "DIY Conan Center"
    url = "https://github.com/Thalhammer/jwt-cpp"
    topics = ("c++", "library", "jwt-auth", "jwt-cpp")
    
    def requirements(self):
        # Pull the actual library from Conan Center
        self.requires("jwt-cpp/0.7.0")
    
    def package_id(self):
        # This is a header-only wrapper, so it doesn't depend on settings
        self.info.clear()
    
    def package_info(self):
        # Propagate the dependency information
        self.cpp_info.bindirs = []
        self.cpp_info.libdirs = []
