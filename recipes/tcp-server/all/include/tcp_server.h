#ifndef TCP_SERVER_H
#define TCP_SERVER_H

namespace tcp_server {

class TcpServer {
public:
    TcpServer();
    ~TcpServer();
    
    void initialize();
    bool process();
};

} // namespace tcp_server

#endif // TCP_SERVER_H
