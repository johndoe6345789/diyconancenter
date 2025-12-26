#include <math_lib.h>
#include <iostream>

int main() {
    math_lib::MathLib obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: math-lib is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
