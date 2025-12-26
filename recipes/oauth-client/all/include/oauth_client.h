#ifndef OAUTH_CLIENT_H
#define OAUTH_CLIENT_H

namespace oauth_client {

class OauthClient {
public:
    OauthClient();
    ~OauthClient();
    
    void initialize();
    bool process();
};

} // namespace oauth_client

#endif // OAUTH_CLIENT_H
