#ifndef HTML_SANITIZER_H
#define HTML_SANITIZER_H

namespace html_sanitizer {

class HtmlSanitizer {
public:
    HtmlSanitizer();
    ~HtmlSanitizer();
    
    void initialize();
    bool process();
};

} // namespace html_sanitizer

#endif // HTML_SANITIZER_H
