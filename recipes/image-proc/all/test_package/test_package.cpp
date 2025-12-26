#include <image_proc.h>
#include <iostream>

int main() {
    image_proc::ImageProc obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: image-proc is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
