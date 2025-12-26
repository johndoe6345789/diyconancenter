#include <stack.h>
#include <iostream>

int main() {
    stack::Stack obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: stack is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
