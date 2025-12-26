#include <tree.h>
#include <iostream>

int main() {
    tree::Tree obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: tree is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
