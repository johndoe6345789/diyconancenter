#include <uuid_generator.h>
#include <iostream>

int main() {
    uuid_generator::UuidGenerator obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: uuid-generator is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
