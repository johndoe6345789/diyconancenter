#include <vector_math.h>
#include <iostream>

int main() {
    vector_math::VectorMath obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: vector-math is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
