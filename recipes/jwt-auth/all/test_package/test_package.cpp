#include <jwt_auth.h>
#include <iostream>

int main() {
    jwt_auth::JwtAuth obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: jwt-auth is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
