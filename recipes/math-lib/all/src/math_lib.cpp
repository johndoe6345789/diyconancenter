#include "math_lib.h"
#include <boost/math/special_functions/factorials.hpp>
#include <boost/math/common_factor.hpp>
#include <boost/math/special_functions/prime.hpp>
#include <boost/math/special_functions/pow.hpp>
#include <cmath>
#include <iostream>

namespace math_lib {

// Pimpl implementation - hides Boost dependency from users
class MathLib::Impl {
public:
    // No state needed for these utility functions
};

MathLib::MathLib() : pImpl(std::make_unique<Impl>()) {
    // Constructor
}

MathLib::~MathLib() = default;

void MathLib::initialize() {
    std::cout << "Math library initialized (Boost.Math backend)" << std::endl;
}

bool MathLib::process() {
    std::cout << "Math library ready (using Boost for mathematical operations)" << std::endl;
    return true;
}

double MathLib::power(double base, double exponent) {
    return boost::math::pow<2>(base); // For simple power operations, or use std::pow
}

double MathLib::sqrt(double x) {
    return std::sqrt(x);
}

double MathLib::cbrt(double x) {
    return std::cbrt(x);
}

long long MathLib::factorial(int n) {
    if (n < 0 || n > 20) return -1; // Limit to prevent overflow
    return boost::math::factorial<double>(static_cast<unsigned>(n));
}

long long MathLib::gcd(long long a, long long b) {
    return boost::math::gcd(a, b);
}

long long MathLib::lcm(long long a, long long b) {
    return boost::math::lcm(a, b);
}

bool MathLib::isPrime(int n) {
    if (n < 2) return false;
    return boost::math::prime(n) == static_cast<unsigned>(n);
}

double MathLib::sin(double x) {
    return std::sin(x);
}

double MathLib::cos(double x) {
    return std::cos(x);
}

double MathLib::tan(double x) {
    return std::tan(x);
}

double MathLib::abs(double x) {
    return std::abs(x);
}

double MathLib::round(double x) {
    return std::round(x);
}

double MathLib::floor(double x) {
    return std::floor(x);
}

double MathLib::ceil(double x) {
    return std::ceil(x);
}

} // namespace math_lib
