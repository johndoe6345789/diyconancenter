#include <string_utils.h>
#include <iostream>
#include <cassert>

int main() {
    string_utils::StringUtils utils;
    utils.initialize();
    
    // Test trim functions
    assert(utils.trim("  hello  ") == "hello");
    assert(utils.trimLeft("  hello") == "hello");
    assert(utils.trimRight("hello  ") == "hello");
    
    // Test split and join
    auto parts = utils.split("one,two,three", ",");
    assert(parts.size() == 3);
    assert(parts[0] == "one");
    assert(parts[1] == "two");
    assert(parts[2] == "three");
    assert(utils.join(parts, "-") == "one-two-three");
    
    // Test case conversion
    assert(utils.toUpper("hello") == "HELLO");
    assert(utils.toLower("WORLD") == "world");
    
    // Test predicates
    assert(utils.startsWith("hello world", "hello"));
    assert(utils.endsWith("hello world", "world"));
    assert(utils.contains("hello world", "lo wo"));
    assert(!utils.startsWith("hello world", "world"));
    
    // Test replace
    assert(utils.replace("hello world world", "world", "universe") == "hello universe world");
    assert(utils.replaceAll("hello world world", "world", "universe") == "hello universe universe");
    
    if (utils.process()) {
        std::cout << "Test passed: All string-utils functions working correctly!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
