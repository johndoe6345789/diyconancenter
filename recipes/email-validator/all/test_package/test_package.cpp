#include <email_validator.h>
#include <iostream>

int main() {
    email_validator::EmailValidator obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: email-validator is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
