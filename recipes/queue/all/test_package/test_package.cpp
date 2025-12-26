#include <queue.h>
#include <iostream>

int main() {
    queue::Queue obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: queue is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
