#include <udp_socket.h>
#include <iostream>

int main() {
    udp_socket::UdpSocket obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: udp-socket is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
