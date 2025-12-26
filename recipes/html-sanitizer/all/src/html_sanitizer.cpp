#include "html_sanitizer.h"
#include <iostream>

namespace html_sanitizer {

HtmlSanitizer::HtmlSanitizer() {
    // Constructor
}

HtmlSanitizer::~HtmlSanitizer() {
    // Destructor
}

void HtmlSanitizer::initialize() {
    std::cout << "Initializing html-sanitizer..." << std::endl;
}

bool HtmlSanitizer::process() {
    std::cout << "Processing with html-sanitizer..." << std::endl;
    return true;
}

} // namespace html_sanitizer
