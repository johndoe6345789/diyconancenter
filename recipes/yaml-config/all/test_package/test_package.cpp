#include <yaml_config.h>
#include <iostream>

int main() {
    yaml_config::YamlConfig obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: yaml-config is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
