#ifndef CRYPTO_UTILS_H
#define CRYPTO_UTILS_H

namespace crypto_utils {

class CryptoUtils {
public:
    CryptoUtils();
    ~CryptoUtils();
    
    void initialize();
    bool process();
};

} // namespace crypto_utils

#endif // CRYPTO_UTILS_H
