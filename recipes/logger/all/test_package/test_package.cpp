#include <logger.h>
#include <iostream>

int main() {
    logger::Logger obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: logger is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
