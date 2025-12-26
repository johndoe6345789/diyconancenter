#ifndef BARCODE_READER_H
#define BARCODE_READER_H

namespace barcode_reader {

class BarcodeReader {
public:
    BarcodeReader();
    ~BarcodeReader();
    
    void initialize();
    bool process();
};

} // namespace barcode_reader

#endif // BARCODE_READER_H
