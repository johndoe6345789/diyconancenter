#ifndef JWT_AUTH_H
#define JWT_AUTH_H

namespace jwt_auth {

class JwtAuth {
public:
    JwtAuth();
    ~JwtAuth();
    
    void initialize();
    bool process();
};

} // namespace jwt_auth

#endif // JWT_AUTH_H
