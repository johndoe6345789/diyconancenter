#include <database_connector.h>
#include <iostream>

int main() {
    database_connector::DatabaseConnector obj;
    obj.initialize();
    
    if (obj.process()) {
        std::cout << "Test passed: database-connector is working!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
