#ifndef MATH_LIB_H
#define MATH_LIB_H

#include <memory>

namespace math_lib {

class MathLib {
public:
    MathLib();
    ~MathLib();
    
    void initialize();
    bool process();
    
    // Clean mathematical API (hiding Boost.Math complexity)
    double power(double base, double exponent);
    double sqrt(double x);
    double cbrt(double x);
    
    long long factorial(int n);
    long long gcd(long long a, long long b);
    long long lcm(long long a, long long b);
    
    bool isPrime(int n);
    
    double sin(double x);
    double cos(double x);
    double tan(double x);
    
    double abs(double x);
    double round(double x);
    double floor(double x);
    double ceil(double x);

private:
    class Impl;
    std::unique_ptr<Impl> pImpl;
};

} // namespace math_lib

#endif // MATH_LIB_H
