#include <timer.h>
#include <iostream>

int main() {
    timer::Timer obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: timer is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
