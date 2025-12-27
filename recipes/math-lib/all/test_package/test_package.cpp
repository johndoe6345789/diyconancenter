#include <math_lib.h>
#include <iostream>
#include <cassert>
#include <cmath>

int main() {
    math_lib::MathLib math;
    math.initialize();
    
    // Test basic operations
    assert(std::abs(math.sqrt(16.0) - 4.0) < 0.001);
    assert(std::abs(math.cbrt(27.0) - 3.0) < 0.001);
    
    // Test factorial
    assert(math.factorial(5) == 120);
    assert(math.factorial(0) == 1);
    
    // Test gcd and lcm
    assert(math.gcd(48, 18) == 6);
    assert(math.lcm(4, 6) == 12);
    
    // Test trigonometry
    assert(std::abs(math.sin(0.0)) < 0.001);
    assert(std::abs(math.cos(0.0) - 1.0) < 0.001);
    
    // Test rounding functions
    assert(math.abs(-5.5) == 5.5);
    assert(math.round(3.7) == 4.0);
    assert(math.floor(3.7) == 3.0);
    assert(math.ceil(3.2) == 4.0);
    
    if (math.process()) {
        std::cout << "Test passed: All math-lib functions working correctly!" << std::endl;
        return 0;
    }
    
    std::cerr << "Test failed!" << std::endl;
    return 1;
}
