#ifndef VIDEO_DECODER_H
#define VIDEO_DECODER_H

namespace video_decoder {

class VideoDecoder {
public:
    VideoDecoder();
    ~VideoDecoder();
    
    void initialize();
    bool process();
};

} // namespace video_decoder

#endif // VIDEO_DECODER_H
