#include <sorting.h>
#include <iostream>

int main() {
    sorting::Sorting obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: sorting is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
