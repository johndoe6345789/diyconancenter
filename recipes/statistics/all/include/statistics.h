#ifndef STATISTICS_H
#define STATISTICS_H

#include <vector>
#include <memory>

namespace statistics {

class Statistics {
public:
    Statistics();
    ~Statistics();
    
    void initialize();
    bool process();
    
    // Clean statistical API (hiding Boost.Accumulators complexity)
    double mean(const std::vector<double>& data);
    double median(const std::vector<double>& data);
    double variance(const std::vector<double>& data);
    double standardDeviation(const std::vector<double>& data);
    double min(const std::vector<double>& data);
    double max(const std::vector<double>& data);
    double sum(const std::vector<double>& data);
    size_t count(const std::vector<double>& data);

private:
    class Impl;
    std::unique_ptr<Impl> pImpl;
};

} // namespace statistics

#endif // STATISTICS_H
