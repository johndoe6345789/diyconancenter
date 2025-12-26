#include <encryption.h>
#include <iostream>

int main() {
    encryption::Encryption obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: encryption is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
