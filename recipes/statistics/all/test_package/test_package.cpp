#include <statistics.h>
#include <iostream>
#include <cassert>
#include <cmath>

int main() {
    statistics::Statistics stats;
    stats.initialize();
    
    // Test data
    std::vector<double> data = {1.0, 2.0, 3.0, 4.0, 5.0};
    
    // Test mean
    assert(std::abs(stats.mean(data) - 3.0) < 0.001);
    
    // Test median
    assert(std::abs(stats.median(data) - 3.0) < 0.001);
    
    // Test min and max
    assert(std::abs(stats.min(data) - 1.0) < 0.001);
    assert(std::abs(stats.max(data) - 5.0) < 0.001);
    
    // Test sum and count
    assert(std::abs(stats.sum(data) - 15.0) < 0.001);
    assert(stats.count(data) == 5);
    
    // Test variance (variance of 1,2,3,4,5 is 2.5)
    assert(std::abs(stats.variance(data) - 2.5) < 0.1);
    
    // Test standard deviation (sqrt of variance)
    assert(std::abs(stats.standardDeviation(data) - std::sqrt(2.5)) < 0.1);
    
    if (stats.process()) {
        std::cout << "Test passed: All statistics functions working correctly!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
