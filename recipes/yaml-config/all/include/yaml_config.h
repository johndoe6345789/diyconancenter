#ifndef YAML_CONFIG_H
#define YAML_CONFIG_H

namespace yaml_config {

class YamlConfig {
public:
    YamlConfig();
    ~YamlConfig();
    
    void initialize();
    bool process();
};

} // namespace yaml_config

#endif // YAML_CONFIG_H
