#ifndef WEBSOCKET_H
#define WEBSOCKET_H

namespace websocket {

class Websocket {
public:
    Websocket();
    ~Websocket();
    
    void initialize();
    bool process();
};

} // namespace websocket

#endif // WEBSOCKET_H
