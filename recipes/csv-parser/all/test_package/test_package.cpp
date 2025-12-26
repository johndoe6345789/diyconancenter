#include <csv_parser.h>
#include <iostream>

int main() {
    csv_parser::CsvParser obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: csv-parser is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
