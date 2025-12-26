#include <hash_functions.h>
#include <iostream>

int main() {
    hash_functions::HashFunctions obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: hash-functions is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
