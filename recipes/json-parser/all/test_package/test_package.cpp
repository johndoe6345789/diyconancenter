#include <nlohmann/json.hpp>
#include <iostream>

int main() {
    try {
        // Create a JSON object using nlohmann_json
        nlohmann::json j;
        j["name"] = "DIY Conan Center";
        j["version"] = "3.11.3";
        j["real_library"] = true;
        
        std::string json_str = j.dump();
        std::cout << "JSON created: " << json_str << std::endl;
        
        auto parsed = nlohmann::json::parse(json_str);
        if (parsed["real_library"] == true) {
            std::cout << "Test passed: json-parser (nlohmann_json) is working!" << std::endl;
            return 0;
        }
    } catch (const std::exception& e) {
        std::cerr << "Test failed: " << e.what() << std::endl;
        return 1;
    }
    return 1;
}
