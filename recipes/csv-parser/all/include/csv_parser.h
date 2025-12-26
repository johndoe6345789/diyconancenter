#ifndef CSV_PARSER_H
#define CSV_PARSER_H

namespace csv_parser {

class CsvParser {
public:
    CsvParser();
    ~CsvParser();
    
    void initialize();
    bool process();
};

} // namespace csv_parser

#endif // CSV_PARSER_H
