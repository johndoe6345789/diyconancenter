#include <datetime_utils.h>
#include <iostream>

int main() {
    datetime_utils::DatetimeUtils obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: datetime-utils is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
