#include <queue.h>
#include <iostream>
#include <cassert>

int main() {
    queue::Queue<int> q(128);
    q.initialize();
    
    // Test empty queue
    assert(q.empty());
    assert(!q.pop().has_value());
    
    // Test push and pop
    assert(q.push(10));
    assert(q.push(20));
    assert(q.push(30));
    
    // Queue should not be empty now
    assert(!q.empty());
    
    // Test pop order (FIFO)
    auto val1 = q.pop();
    assert(val1.has_value() && val1.value() == 10);
    
    auto val2 = q.pop();
    assert(val2.has_value() && val2.value() == 20);
    
    auto val3 = q.pop();
    assert(val3.has_value() && val3.value() == 30);
    
    // Queue should be empty again
    assert(q.empty());
    assert(!q.pop().has_value());
    
    if (q.process()) {
        std::cout << "Test passed: Thread-safe queue working correctly!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
