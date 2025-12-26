#include <random_gen.h>
#include <iostream>

int main() {
    random_gen::RandomGen obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: random-gen is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
