#include <qr_code.h>
#include <iostream>

int main() {
    qr_code::QrCode obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: qr-code is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
