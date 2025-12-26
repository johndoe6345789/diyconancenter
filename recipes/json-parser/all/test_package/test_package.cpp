#include <json_parser.h>
#include <iostream>

int main() {
    json_parser::JsonParser obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: json-parser is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
