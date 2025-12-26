#ifndef TIMER_H
#define TIMER_H

namespace timer {

class Timer {
public:
    Timer();
    ~Timer();
    
    void initialize();
    bool process();
};

} // namespace timer

#endif // TIMER_H
