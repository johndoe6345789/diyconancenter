#include <cache_manager.h>
#include <iostream>

int main() {
    cache_manager::CacheManager obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: cache-manager is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
