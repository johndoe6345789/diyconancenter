#ifndef ENCRYPTION_H
#define ENCRYPTION_H

#include <string>
#include <vector>
#include <memory>

namespace encryption {

class Encryption {
public:
    Encryption();
    ~Encryption();
    
    void initialize();
    bool process();
    
    // Clean encryption API (hiding Libsodium complexity)
    std::string generateKey();
    std::vector<unsigned char> encrypt(const std::string& plaintext, const std::string& key);
    std::string decrypt(const std::vector<unsigned char>& ciphertext, const std::string& key);
    
    std::string hash(const std::string& data);
    bool verifyHash(const std::string& data, const std::string& hash);

private:
    class Impl;
    std::unique_ptr<Impl> pImpl;
};

} // namespace encryption

#endif // ENCRYPTION_H
