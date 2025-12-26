from conan import ConanFile


class DatetimeutilsConan(ConanFile):
    name = "datetime-utils"
    version = "3.0.1"
    description = "Wrapper for date from Conan Center"
    license = "MIT"
    author = "DIY Conan Center"
    url = "https://github.com/HowardHinnant/date"
    topics = ("c++", "library", "datetime-utils", "date")
    
    def requirements(self):
        # Pull the actual library from Conan Center
        self.requires("date/3.0.1")
    
    def package_id(self):
        # This is a header-only wrapper, so it doesn't depend on settings
        self.info.clear()
    
    def package_info(self):
        # Propagate the dependency information
        self.cpp_info.bindirs = []
        self.cpp_info.libdirs = []
