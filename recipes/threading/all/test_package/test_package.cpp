#include <threading.h>
#include <iostream>

int main() {
    threading::Threading obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: threading is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
