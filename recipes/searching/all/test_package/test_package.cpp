#include <searching.h>
#include <iostream>

int main() {
    searching::Searching obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: searching is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
