#include "tcp_server.h"
#include <iostream>

namespace tcp_server {

TcpServer::TcpServer() {
    // Constructor
}

TcpServer::~TcpServer() {
    // Destructor
}

void TcpServer::initialize() {
    std::cout << "Initializing tcp-server..." << std::endl;
}

bool TcpServer::process() {
    std::cout << "Processing with tcp-server..." << std::endl;
    return true;
}

} // namespace tcp_server
