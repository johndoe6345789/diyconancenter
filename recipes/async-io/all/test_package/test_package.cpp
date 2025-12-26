#include <async_io.h>
#include <iostream>

int main() {
    async_io::AsyncIo obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: async-io is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
