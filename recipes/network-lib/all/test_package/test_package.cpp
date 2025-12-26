#include <network_lib.h>
#include <iostream>

int main() {
    network_lib::NetworkLib obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: network-lib is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
