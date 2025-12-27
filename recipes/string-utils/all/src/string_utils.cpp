#include "string_utils.h"
#include <boost/algorithm/string.hpp>
#include <iostream>

namespace string_utils {

// Pimpl implementation - hides Boost dependency from users
class StringUtils::Impl {
public:
    // No state needed for these utility functions
};

StringUtils::StringUtils() : pImpl(std::make_unique<Impl>()) {
    // Constructor
}

StringUtils::~StringUtils() = default;

void StringUtils::initialize() {
    std::cout << "String utilities initialized (Boost.Algorithm backend)" << std::endl;
}

bool StringUtils::process() {
    std::cout << "String utilities ready (using Boost for string operations)" << std::endl;
    return true;
}

std::string StringUtils::trim(const std::string& str) {
    return boost::algorithm::trim_copy(str);
}

std::string StringUtils::trimLeft(const std::string& str) {
    return boost::algorithm::trim_left_copy(str);
}

std::string StringUtils::trimRight(const std::string& str) {
    return boost::algorithm::trim_right_copy(str);
}

std::vector<std::string> StringUtils::split(const std::string& str, const std::string& delimiter) {
    std::vector<std::string> result;
    boost::algorithm::split(result, str, boost::algorithm::is_any_of(delimiter));
    return result;
}

std::string StringUtils::join(const std::vector<std::string>& strings, const std::string& delimiter) {
    return boost::algorithm::join(strings, delimiter);
}

std::string StringUtils::toUpper(const std::string& str) {
    return boost::algorithm::to_upper_copy(str);
}

std::string StringUtils::toLower(const std::string& str) {
    return boost::algorithm::to_lower_copy(str);
}

bool StringUtils::startsWith(const std::string& str, const std::string& prefix) {
    return boost::algorithm::starts_with(str, prefix);
}

bool StringUtils::endsWith(const std::string& str, const std::string& suffix) {
    return boost::algorithm::ends_with(str, suffix);
}

bool StringUtils::contains(const std::string& str, const std::string& substring) {
    return boost::algorithm::contains(str, substring);
}

std::string StringUtils::replace(const std::string& str, const std::string& from, const std::string& to) {
    return boost::algorithm::replace_first_copy(str, from, to);
}

std::string StringUtils::replaceAll(const std::string& str, const std::string& from, const std::string& to) {
    return boost::algorithm::replace_all_copy(str, from, to);
}

} // namespace string_utils
