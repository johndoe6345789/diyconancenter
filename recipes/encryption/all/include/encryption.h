#ifndef ENCRYPTION_H
#define ENCRYPTION_H

namespace encryption {

class Encryption {
public:
    Encryption();
    ~Encryption();
    
    void initialize();
    bool process();
};

} // namespace encryption

#endif // ENCRYPTION_H
