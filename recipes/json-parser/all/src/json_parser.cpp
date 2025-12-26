#include "json_parser.h"
#include <nlohmann/json.hpp>
#include <iostream>

namespace json_parser {

class JsonParser::Impl {
public:
    nlohmann::json data;
};

JsonParser::JsonParser() : pImpl(std::make_unique<Impl>()) {
    // Constructor
}

JsonParser::~JsonParser() = default;

void JsonParser::initialize() {
    std::cout << "Initializing json-parser with nlohmann_json backend..." << std::endl;
    pImpl->data = nlohmann::json::object();
    pImpl->data["initialized"] = true;
}

bool JsonParser::process() {
    std::cout << "Processing with json-parser (nlohmann_json backend)..." << std::endl;
    pImpl->data["processed"] = true;
    std::string output = pImpl->data.dump();
    std::cout << "JSON: " << output << std::endl;
    return true;
}

} // namespace json_parser
