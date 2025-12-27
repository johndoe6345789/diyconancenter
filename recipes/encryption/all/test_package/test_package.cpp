#include <encryption.h>
#include <iostream>
#include <cassert>

int main() {
    encryption::Encryption enc;
    enc.initialize();
    
    // Test key generation
    std::string key = enc.generateKey();
    assert(!key.empty());
    std::cout << "Generated key length: " << key.length() << std::endl;
    
    // Test encryption and decryption
    std::string plaintext = "Hello, World!";
    auto ciphertext = enc.encrypt(plaintext, key);
    assert(!ciphertext.empty());
    std::cout << "Ciphertext size: " << ciphertext.size() << std::endl;
    
    std::string decrypted = enc.decrypt(ciphertext, key);
    assert(decrypted == plaintext);
    std::cout << "Decrypted: " << decrypted << std::endl;
    
    // Test hashing
    std::string data = "test data";
    std::string hashVal = enc.hash(data);
    assert(!hashVal.empty());
    std::cout << "Hash: " << hashVal << std::endl;
    
    // Test hash verification
    assert(enc.verifyHash(data, hashVal));
    assert(!enc.verifyHash("wrong data", hashVal));
    
    if (enc.process()) {
        std::cout << "Test passed: All encryption functions working correctly!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
