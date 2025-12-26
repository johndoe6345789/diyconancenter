#include <logger.h>
#include <iostream>

int main() {
    // Use the uniform API
    logger::Logger obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: logger (with spdlog backend) is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
