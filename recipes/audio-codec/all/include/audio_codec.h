#ifndef AUDIO_CODEC_H
#define AUDIO_CODEC_H

namespace audio_codec {

class AudioCodec {
public:
    AudioCodec();
    ~AudioCodec();
    
    void initialize();
    bool process();
};

} // namespace audio_codec

#endif // AUDIO_CODEC_H
