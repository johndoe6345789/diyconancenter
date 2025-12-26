#ifndef HTTP_CLIENT_H
#define HTTP_CLIENT_H

namespace http_client {

class HttpClient {
public:
    HttpClient();
    ~HttpClient();
    
    void initialize();
    bool process();
};

} // namespace http_client

#endif // HTTP_CLIENT_H
