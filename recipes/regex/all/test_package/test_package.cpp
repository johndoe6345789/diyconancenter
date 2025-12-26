#include <regex.h>
#include <iostream>

int main() {
    regex::Regex obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: regex is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
