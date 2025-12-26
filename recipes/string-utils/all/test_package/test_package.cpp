#include <string_utils.h>
#include <iostream>

int main() {
    string_utils::StringUtils obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: string-utils is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
