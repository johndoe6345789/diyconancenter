#include <serialization.h>
#include <iostream>

int main() {
    serialization::Serialization obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: serialization is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
