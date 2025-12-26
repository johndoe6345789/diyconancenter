#include <tcp_server.h>
#include <iostream>

int main() {
    tcp_server::TcpServer obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: tcp-server is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
