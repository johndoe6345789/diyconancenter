#ifndef NETWORK_LIB_H
#define NETWORK_LIB_H

namespace network_lib {

class NetworkLib {
public:
    NetworkLib();
    ~NetworkLib();
    
    void initialize();
    bool process();
};

} // namespace network_lib

#endif // NETWORK_LIB_H
