#include <graph.h>
#include <iostream>

int main() {
    graph::Graph obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: graph is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
