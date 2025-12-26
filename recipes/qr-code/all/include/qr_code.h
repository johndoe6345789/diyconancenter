#ifndef QR_CODE_H
#define QR_CODE_H

namespace qr_code {

class QrCode {
public:
    QrCode();
    ~QrCode();
    
    void initialize();
    bool process();
};

} // namespace qr_code

#endif // QR_CODE_H
