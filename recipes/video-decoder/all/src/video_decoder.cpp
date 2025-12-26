#include "video_decoder.h"
#include <iostream>

namespace video_decoder {

VideoDecoder::VideoDecoder() {
    // Constructor
}

VideoDecoder::~VideoDecoder() {
    // Destructor
}

void VideoDecoder::initialize() {
    std::cout << "Initializing video-decoder..." << std::endl;
}

bool VideoDecoder::process() {
    std::cout << "Processing with video-decoder..." << std::endl;
    return true;
}

} // namespace video_decoder
