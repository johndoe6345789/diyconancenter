#include <compression.h>
#include <iostream>

int main() {
    compression::Compression obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: compression is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
