#include <websocket.h>
#include <iostream>

int main() {
    websocket::Websocket obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: websocket is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
