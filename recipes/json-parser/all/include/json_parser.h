#ifndef JSON_PARSER_H
#define JSON_PARSER_H

#include <memory>

namespace json_parser {

class JsonParser {
public:
    JsonParser();
    ~JsonParser();
    
    void initialize();
    bool process();
    
private:
    class Impl;
    std::unique_ptr<Impl> pImpl;
};

} // namespace json_parser

#endif // JSON_PARSER_H
