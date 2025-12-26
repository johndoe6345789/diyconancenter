#include <crypto_utils.h>
#include <iostream>

int main() {
    crypto_utils::CryptoUtils obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: crypto-utils is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
