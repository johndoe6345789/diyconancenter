#include <json_parser.h>
#include <iostream>

int main() {
    // Use the uniform API
    json_parser::JsonParser obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: json-parser (with nlohmann_json backend) is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
