#ifndef MARKDOWN_PARSER_H
#define MARKDOWN_PARSER_H

namespace markdown_parser {

class MarkdownParser {
public:
    MarkdownParser();
    ~MarkdownParser();
    
    void initialize();
    bool process();
};

} // namespace markdown_parser

#endif // MARKDOWN_PARSER_H
