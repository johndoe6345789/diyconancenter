#ifndef QUEUE_H
#define QUEUE_H

#include <memory>
#include <optional>

namespace queue {

template<typename T>
class Queue {
public:
    Queue(size_t capacity = 128);
    ~Queue();
    
    void initialize();
    bool process();
    
    // Clean queue API (hiding Boost.Lockfree complexity)
    bool push(const T& item);
    std::optional<T> pop();
    bool empty() const;
    // Note: size() is not available for lock-free queues

private:
    class Impl;
    std::unique_ptr<Impl> pImpl;
};

} // namespace queue

#endif // QUEUE_H
