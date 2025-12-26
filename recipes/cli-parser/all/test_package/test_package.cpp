#include <cli_parser.h>
#include <iostream>

int main() {
    cli_parser::CliParser obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: cli-parser is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
