#include <audio_codec.h>
#include <iostream>

int main() {
    audio_codec::AudioCodec obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: audio-codec is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
