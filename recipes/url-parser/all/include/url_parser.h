#ifndef URL_PARSER_H
#define URL_PARSER_H

namespace url_parser {

class UrlParser {
public:
    UrlParser();
    ~UrlParser();
    
    void initialize();
    bool process();
};

} // namespace url_parser

#endif // URL_PARSER_H
