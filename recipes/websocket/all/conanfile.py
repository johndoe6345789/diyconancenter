from conan import ConanFile


class WebsocketConan(ConanFile):
    name = "websocket"
    version = "0.8.2"
    description = "Wrapper for websocketpp from Conan Center"
    license = "MIT"
    author = "DIY Conan Center"
    url = "https://github.com/zaphoyd/websocketpp"
    topics = ("c++", "library", "websocket", "websocketpp")
    
    def requirements(self):
        # Pull the actual library from Conan Center
        self.requires("websocketpp/0.8.2")
    
    def package_id(self):
        # This is a header-only wrapper, so it doesn't depend on settings
        self.info.clear()
    
    def package_info(self):
        # Propagate the dependency information
        self.cpp_info.bindirs = []
        self.cpp_info.libdirs = []
