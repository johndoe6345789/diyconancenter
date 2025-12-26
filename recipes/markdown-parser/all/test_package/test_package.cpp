#include <markdown_parser.h>
#include <iostream>

int main() {
    markdown_parser::MarkdownParser obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: markdown-parser is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
