#include <geometry.h>
#include <iostream>

int main() {
    geometry::Geometry obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: geometry is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
