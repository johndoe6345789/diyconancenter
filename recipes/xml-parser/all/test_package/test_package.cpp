#include <xml_parser.h>
#include <iostream>

int main() {
    xml_parser::XmlParser obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: xml-parser is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
