#include <oauth_client.h>
#include <iostream>

int main() {
    oauth_client::OauthClient obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: oauth-client is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
