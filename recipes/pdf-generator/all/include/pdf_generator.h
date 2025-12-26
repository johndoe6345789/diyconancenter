#ifndef PDF_GENERATOR_H
#define PDF_GENERATOR_H

namespace pdf_generator {

class PdfGenerator {
public:
    PdfGenerator();
    ~PdfGenerator();
    
    void initialize();
    bool process();
};

} // namespace pdf_generator

#endif // PDF_GENERATOR_H
