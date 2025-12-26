#ifndef COMPRESSION_H
#define COMPRESSION_H

namespace compression {

class Compression {
public:
    Compression();
    ~Compression();
    
    void initialize();
    bool process();
};

} // namespace compression

#endif // COMPRESSION_H
