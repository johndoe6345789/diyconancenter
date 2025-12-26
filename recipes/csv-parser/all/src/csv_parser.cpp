#include "csv_parser.h"
#include <iostream>

namespace csv_parser {

CsvParser::CsvParser() {
    // Constructor
}

CsvParser::~CsvParser() {
    // Destructor
}

void CsvParser::initialize() {
    std::cout << "Initializing csv-parser..." << std::endl;
}

bool CsvParser::process() {
    std::cout << "Processing with csv-parser..." << std::endl;
    return true;
}

} // namespace csv_parser
