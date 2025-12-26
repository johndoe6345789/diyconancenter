#ifndef ASYNC_IO_H
#define ASYNC_IO_H

namespace async_io {

class AsyncIo {
public:
    AsyncIo();
    ~AsyncIo();
    
    void initialize();
    bool process();
};

} // namespace async_io

#endif // ASYNC_IO_H
