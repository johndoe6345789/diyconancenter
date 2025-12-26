#include <video_decoder.h>
#include <iostream>

int main() {
    video_decoder::VideoDecoder obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: video-decoder is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
