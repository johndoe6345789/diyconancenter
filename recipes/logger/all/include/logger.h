#ifndef LOGGER_H
#define LOGGER_H

#include <memory>

namespace logger {

class Logger {
public:
    Logger();
    ~Logger();
    
    void initialize();
    bool process();
    
private:
    class Impl;
    std::unique_ptr<Impl> pImpl;
};

} // namespace logger

#endif // LOGGER_H
