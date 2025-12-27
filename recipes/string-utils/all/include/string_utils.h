#ifndef STRING_UTILS_H
#define STRING_UTILS_H

#include <string>
#include <vector>
#include <memory>

namespace string_utils {

class StringUtils {
public:
    StringUtils();
    ~StringUtils();
    
    void initialize();
    bool process();
    
    // Clean, simple string manipulation API (hiding Boost complexity)
    std::string trim(const std::string& str);
    std::string trimLeft(const std::string& str);
    std::string trimRight(const std::string& str);
    
    std::vector<std::string> split(const std::string& str, const std::string& delimiter);
    std::string join(const std::vector<std::string>& strings, const std::string& delimiter);
    
    std::string toUpper(const std::string& str);
    std::string toLower(const std::string& str);
    
    bool startsWith(const std::string& str, const std::string& prefix);
    bool endsWith(const std::string& str, const std::string& suffix);
    bool contains(const std::string& str, const std::string& substring);
    
    std::string replace(const std::string& str, const std::string& from, const std::string& to);
    std::string replaceAll(const std::string& str, const std::string& from, const std::string& to);

private:
    class Impl;
    std::unique_ptr<Impl> pImpl;
};

} // namespace string_utils

#endif // STRING_UTILS_H
