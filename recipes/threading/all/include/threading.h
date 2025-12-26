#ifndef THREADING_H
#define THREADING_H

namespace threading {

class Threading {
public:
    Threading();
    ~Threading();
    
    void initialize();
    bool process();
};

} // namespace threading

#endif // THREADING_H
