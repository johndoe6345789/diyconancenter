#ifndef DATABASE_CONNECTOR_H
#define DATABASE_CONNECTOR_H

namespace database_connector {

class DatabaseConnector {
public:
    DatabaseConnector();
    ~DatabaseConnector();
    
    void initialize();
    bool process();
};

} // namespace database_connector

#endif // DATABASE_CONNECTOR_H
