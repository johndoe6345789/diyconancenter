#include <spdlog/spdlog.h>
#include <iostream>

int main() {
    try {
        spdlog::info("Test message from spdlog");
        spdlog::warn("Warning message");
        std::cout << "Test passed: logger (spdlog) is working!" << std::endl;
        return 0;
    } catch (const std::exception& e) {
        std::cerr << "Test failed: " << e.what() << std::endl;
        return 1;
    }
    return 1;
}
