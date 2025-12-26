#ifndef IMAGE_PROC_H
#define IMAGE_PROC_H

namespace image_proc {

class ImageProc {
public:
    ImageProc();
    ~ImageProc();
    
    void initialize();
    bool process();
};

} // namespace image_proc

#endif // IMAGE_PROC_H
