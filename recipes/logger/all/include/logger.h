#ifndef LOGGER_H
#define LOGGER_H

namespace logger {

class Logger {
public:
    Logger();
    ~Logger();
    
    void initialize();
    bool process();
};

} // namespace logger

#endif // LOGGER_H
