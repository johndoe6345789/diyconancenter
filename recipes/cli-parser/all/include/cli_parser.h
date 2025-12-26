#ifndef CLI_PARSER_H
#define CLI_PARSER_H

namespace cli_parser {

class CliParser {
public:
    CliParser();
    ~CliParser();
    
    void initialize();
    bool process();
};

} // namespace cli_parser

#endif // CLI_PARSER_H
