#include <html_sanitizer.h>
#include <iostream>

int main() {
    html_sanitizer::HtmlSanitizer obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: html-sanitizer is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
