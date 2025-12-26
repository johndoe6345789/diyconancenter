#include <http_client.h>
#include <iostream>

int main() {
    http_client::HttpClient obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: http-client is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
