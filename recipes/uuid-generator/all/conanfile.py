from conan import ConanFile
from conan.tools.cmake import CMakeToolchain, CMake, cmake_layout, CMakeDeps
from conan.tools.files import get, copy


class UuidgeneratorConan(ConanFile):
    name = "uuid-generator"
    version = "1.2.3"
    description = "Real stduuid library - uuid-generator"
    license = "MIT"
    author = "DIY Conan Center"
    url = "https://github.com/mariusbancila/stduuid"
    topics = ("c++", "library", "uuid-generator", "stduuid")
    settings = "os", "compiler", "build_type", "arch"
    options = {"shared": [True, False], "fPIC": [True, False]}
    default_options = {"shared": False, "fPIC": True}
    
    def config_options(self):
        if self.settings.os == "Windows":
            del self.options.fPIC
    
    def configure(self):
        if self.options.shared:
            self.options.rm_safe("fPIC")
    
    def source(self):
        # Download and extract the source code from upstream
        get(self, **self.conan_data["sources"][self.version], 
            destination=self.source_folder, strip_root=True)
    
    def layout(self):
        cmake_layout(self, src_folder="src")
    
    def generate(self):
        tc = CMakeToolchain(self)
        tc.generate()
        deps = CMakeDeps(self)
        deps.generate()
    
    def build(self):
        cmake = CMake(self)
        cmake.configure()
        cmake.build()
    
    def package(self):
        cmake = CMake(self)
        cmake.install()
        # Copy license files
        copy(self, "LICENSE*", src=self.source_folder, dst=os.path.join(self.package_folder, "licenses"))
    
    def package_info(self):
        self.cpp_info.libs = ["uuid_generator"]
