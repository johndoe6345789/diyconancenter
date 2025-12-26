#include <barcode_reader.h>
#include <iostream>

int main() {
    barcode_reader::BarcodeReader obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: barcode-reader is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
