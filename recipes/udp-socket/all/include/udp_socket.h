#ifndef UDP_SOCKET_H
#define UDP_SOCKET_H

namespace udp_socket {

class UdpSocket {
public:
    UdpSocket();
    ~UdpSocket();
    
    void initialize();
    bool process();
};

} // namespace udp_socket

#endif // UDP_SOCKET_H
