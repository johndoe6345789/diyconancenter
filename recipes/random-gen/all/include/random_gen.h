#ifndef RANDOM_GEN_H
#define RANDOM_GEN_H

namespace random_gen {

class RandomGen {
public:
    RandomGen();
    ~RandomGen();
    
    void initialize();
    bool process();
};

} // namespace random_gen

#endif // RANDOM_GEN_H
