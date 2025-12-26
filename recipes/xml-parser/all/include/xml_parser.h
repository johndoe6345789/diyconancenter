#ifndef XML_PARSER_H
#define XML_PARSER_H

namespace xml_parser {

class XmlParser {
public:
    XmlParser();
    ~XmlParser();
    
    void initialize();
    bool process();
};

} // namespace xml_parser

#endif // XML_PARSER_H
