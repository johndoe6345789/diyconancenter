#include "statistics.h"
#include <boost/accumulators/accumulators.hpp>
#include <boost/accumulators/statistics/stats.hpp>
#include <boost/accumulators/statistics/mean.hpp>
#include <boost/accumulators/statistics/median.hpp>
#include <boost/accumulators/statistics/variance.hpp>
#include <boost/accumulators/statistics/min.hpp>
#include <boost/accumulators/statistics/max.hpp>
#include <boost/accumulators/statistics/sum.hpp>
#include <boost/accumulators/statistics/count.hpp>
#include <algorithm>
#include <cmath>
#include <iostream>
#include <stdexcept>

namespace statistics {

// Pimpl implementation - hides Boost dependency from users
class Statistics::Impl {
public:
    // No state needed for these utility functions
};

Statistics::Statistics() : pImpl(std::make_unique<Impl>()) {
    // Constructor
}

Statistics::~Statistics() = default;

void Statistics::initialize() {
    std::cout << "Statistics library initialized (Boost.Accumulators backend)" << std::endl;
}

bool Statistics::process() {
    std::cout << "Statistics library ready (using Boost for statistical operations)" << std::endl;
    return true;
}

double Statistics::mean(const std::vector<double>& data) {
    if (data.empty()) return 0.0;
    
    using namespace boost::accumulators;
    accumulator_set<double, stats<tag::mean>> acc;
    for (double val : data) {
        acc(val);
    }
    return boost::accumulators::mean(acc);
}

double Statistics::median(const std::vector<double>& data) {
    if (data.empty()) return 0.0;
    
    std::vector<double> sorted = data;
    std::sort(sorted.begin(), sorted.end());
    
    size_t n = sorted.size();
    if (n % 2 == 0) {
        return (sorted[n/2 - 1] + sorted[n/2]) / 2.0;
    } else {
        return sorted[n/2];
    }
}

double Statistics::variance(const std::vector<double>& data) {
    if (data.size() < 2) {
        throw std::invalid_argument("Variance requires at least 2 data points");
    }
    
    using namespace boost::accumulators;
    accumulator_set<double, stats<tag::variance>> acc;
    for (double val : data) {
        acc(val);
    }
    return boost::accumulators::variance(acc);
}

double Statistics::standardDeviation(const std::vector<double>& data) {
    return std::sqrt(variance(data));
}

double Statistics::min(const std::vector<double>& data) {
    if (data.empty()) return 0.0;
    
    using namespace boost::accumulators;
    accumulator_set<double, stats<tag::min>> acc;
    for (double val : data) {
        acc(val);
    }
    return boost::accumulators::min(acc);
}

double Statistics::max(const std::vector<double>& data) {
    if (data.empty()) return 0.0;
    
    using namespace boost::accumulators;
    accumulator_set<double, stats<tag::max>> acc;
    for (double val : data) {
        acc(val);
    }
    return boost::accumulators::max(acc);
}

double Statistics::sum(const std::vector<double>& data) {
    if (data.empty()) return 0.0;
    
    using namespace boost::accumulators;
    accumulator_set<double, stats<tag::sum>> acc;
    for (double val : data) {
        acc(val);
    }
    return boost::accumulators::sum(acc);
}

size_t Statistics::count(const std::vector<double>& data) {
    return data.size();
}

} // namespace statistics
