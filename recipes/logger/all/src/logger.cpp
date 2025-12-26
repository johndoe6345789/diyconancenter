#include "logger.h"
#include <spdlog/spdlog.h>
#include <iostream>

namespace logger {

class Logger::Impl {
public:
    // spdlog is header-only/singleton, no instance needed
};

Logger::Logger() : pImpl(std::make_unique<Impl>()) {
    // Constructor
}

Logger::~Logger() = default;

void Logger::initialize() {
    spdlog::info("Initializing logger with spdlog backend...");
}

bool Logger::process() {
    spdlog::info("Processing with logger (spdlog backend)...");
    spdlog::debug("Debug message");
    spdlog::warn("Warning message");
    return true;
}

} // namespace logger
