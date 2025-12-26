#include <statistics.h>
#include <iostream>

int main() {
    statistics::Statistics obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: statistics is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
