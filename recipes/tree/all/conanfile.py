from conan import ConanFile
from conan.tools.cmake import CMakeToolchain, CMake, cmake_layout


class TreeConan(ConanFile):
    name = "tree"
    version = "1.1.0"
    description = "Tree data structure library"
    license = "MIT"
    author = "DIY Conan Center"
    url = "https://github.com/johndoe6345789/diyconancenter"
    topics = ("c++", "library", "tree")
    settings = "os", "compiler", "build_type", "arch"
    options = {"shared": [True, False], "fPIC": [True, False]}
    default_options = {"shared": False, "fPIC": True}
    exports_sources = "CMakeLists.txt", "src/*", "include/*"
    
    def config_options(self):
        if self.settings.os == "Windows":
            del self.options.fPIC
    
    def configure(self):
        if self.options.shared:
            self.options.rm_safe("fPIC")
    
    def layout(self):
        cmake_layout(self)
    
    def generate(self):
        tc = CMakeToolchain(self)
        tc.generate()
    
    def build(self):
        cmake = CMake(self)
        cmake.configure()
        cmake.build()
    
    def package(self):
        cmake = CMake(self)
        cmake.install()
    
    def package_info(self):
        self.cpp_info.libs = ["tree"]
