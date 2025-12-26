#ifndef INI_READER_H
#define INI_READER_H

namespace ini_reader {

class IniReader {
public:
    IniReader();
    ~IniReader();
    
    void initialize();
    bool process();
};

} // namespace ini_reader

#endif // INI_READER_H
