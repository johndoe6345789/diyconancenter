#include "image_proc.h"
#include <iostream>

namespace image_proc {

ImageProc::ImageProc() {
    // Constructor
}

ImageProc::~ImageProc() {
    // Destructor
}

void ImageProc::initialize() {
    std::cout << "Initializing image-proc..." << std::endl;
}

bool ImageProc::process() {
    std::cout << "Processing with image-proc..." << std::endl;
    return true;
}

} // namespace image_proc
