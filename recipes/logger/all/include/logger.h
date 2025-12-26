#ifndef LOGGER_H
#define LOGGER_H

namespace logger {

class Logger {
public:
    Logger();
    ~Logger();
    
    void initialize();
    bool process();
    
private:
    class Impl;
    Impl* pImpl;
};

} // namespace logger

#endif // LOGGER_H
