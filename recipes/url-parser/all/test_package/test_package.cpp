#include <url_parser.h>
#include <iostream>

int main() {
    url_parser::UrlParser obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: url-parser is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
