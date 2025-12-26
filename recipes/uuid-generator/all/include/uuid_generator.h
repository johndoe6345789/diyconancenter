#ifndef UUID_GENERATOR_H
#define UUID_GENERATOR_H

namespace uuid_generator {

class UuidGenerator {
public:
    UuidGenerator();
    ~UuidGenerator();
    
    void initialize();
    bool process();
};

} // namespace uuid_generator

#endif // UUID_GENERATOR_H
