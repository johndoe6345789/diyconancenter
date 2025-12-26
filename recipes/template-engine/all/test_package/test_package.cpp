#include <template_engine.h>
#include <iostream>

int main() {
    template_engine::TemplateEngine obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: template-engine is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
