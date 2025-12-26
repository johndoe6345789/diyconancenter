#include <pdf_generator.h>
#include <iostream>

int main() {
    pdf_generator::PdfGenerator obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: pdf-generator is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
