#include <ini_reader.h>
#include <iostream>

int main() {
    ini_reader::IniReader obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: ini-reader is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
