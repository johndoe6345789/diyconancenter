#include "encryption.h"
#include <sodium.h>
#include <iostream>
#include <sstream>
#include <iomanip>
#include <stdexcept>

namespace encryption {

// Pimpl implementation - hides Libsodium dependency from users
class Encryption::Impl {
public:
    Impl() {
        if (sodium_init() < 0) {
            throw std::runtime_error("Failed to initialize libsodium");
        }
    }
};

Encryption::Encryption() : pImpl(std::make_unique<Impl>()) {
    // Constructor
}

Encryption::~Encryption() = default;

void Encryption::initialize() {
    std::cout << "Encryption library initialized (Libsodium backend)" << std::endl;
}

bool Encryption::process() {
    std::cout << "Encryption library ready (using Libsodium for secure operations)" << std::endl;
    return true;
}

std::string Encryption::generateKey() {
    unsigned char key[crypto_secretbox_KEYBYTES];
    crypto_secretbox_keygen(key);
    
    // Convert to hex string for easy storage
    std::stringstream ss;
    for (size_t i = 0; i < sizeof(key); ++i) {
        ss << std::hex << std::setw(2) << std::setfill('0') << static_cast<int>(key[i]);
    }
    return ss.str();
}

std::vector<unsigned char> Encryption::encrypt(const std::string& plaintext, const std::string& key) {
    // Convert hex key back to bytes
    if (key.length() != crypto_secretbox_KEYBYTES * 2) {
        throw std::invalid_argument("Invalid key length");
    }
    
    unsigned char keyBytes[crypto_secretbox_KEYBYTES];
    for (size_t i = 0; i < crypto_secretbox_KEYBYTES; ++i) {
        std::string byteString = key.substr(i * 2, 2);
        keyBytes[i] = static_cast<unsigned char>(std::stoi(byteString, nullptr, 16));
    }
    
    // Generate nonce
    unsigned char nonce[crypto_secretbox_NONCEBYTES];
    randombytes_buf(nonce, sizeof(nonce));
    
    // Encrypt
    std::vector<unsigned char> ciphertext(crypto_secretbox_MACBYTES + plaintext.length());
    crypto_secretbox_easy(ciphertext.data(),
                         reinterpret_cast<const unsigned char*>(plaintext.c_str()),
                         plaintext.length(),
                         nonce,
                         keyBytes);
    
    // Prepend nonce to ciphertext
    std::vector<unsigned char> result(sizeof(nonce) + ciphertext.size());
    std::copy(nonce, nonce + sizeof(nonce), result.begin());
    std::copy(ciphertext.begin(), ciphertext.end(), result.begin() + sizeof(nonce));
    
    return result;
}

std::string Encryption::decrypt(const std::vector<unsigned char>& ciphertext, const std::string& key) {
    // Convert hex key back to bytes
    if (key.length() != crypto_secretbox_KEYBYTES * 2) {
        throw std::invalid_argument("Invalid key length");
    }
    
    unsigned char keyBytes[crypto_secretbox_KEYBYTES];
    for (size_t i = 0; i < crypto_secretbox_KEYBYTES; ++i) {
        std::string byteString = key.substr(i * 2, 2);
        keyBytes[i] = static_cast<unsigned char>(std::stoi(byteString, nullptr, 16));
    }
    
    // Extract nonce
    if (ciphertext.size() < crypto_secretbox_NONCEBYTES) {
        throw std::invalid_argument("Ciphertext too short");
    }
    
    unsigned char nonce[crypto_secretbox_NONCEBYTES];
    std::copy(ciphertext.begin(), ciphertext.begin() + crypto_secretbox_NONCEBYTES, nonce);
    
    // Decrypt
    size_t messageLen = ciphertext.size() - crypto_secretbox_NONCEBYTES - crypto_secretbox_MACBYTES;
    std::vector<unsigned char> plaintext(messageLen);
    
    if (crypto_secretbox_open_easy(plaintext.data(),
                                   ciphertext.data() + crypto_secretbox_NONCEBYTES,
                                   ciphertext.size() - crypto_secretbox_NONCEBYTES,
                                   nonce,
                                   keyBytes) != 0) {
        throw std::runtime_error("Decryption failed");
    }
    
    return std::string(plaintext.begin(), plaintext.end());
}

std::string Encryption::hash(const std::string& data) {
    unsigned char hash[crypto_generichash_BYTES];
    crypto_generichash(hash, sizeof(hash),
                      reinterpret_cast<const unsigned char*>(data.c_str()),
                      data.length(),
                      nullptr, 0);
    
    // Convert to hex string
    std::stringstream ss;
    for (size_t i = 0; i < sizeof(hash); ++i) {
        ss << std::hex << std::setw(2) << std::setfill('0') << static_cast<int>(hash[i]);
    }
    return ss.str();
}

bool Encryption::verifyHash(const std::string& data, const std::string& hashStr) {
    return hash(data) == hashStr;
}

} // namespace encryption
