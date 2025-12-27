#include "queue.h"
#include <boost/lockfree/queue.hpp>
#include <iostream>

namespace queue {

// Pimpl implementation - hides Boost dependency from users
template<typename T>
class Queue<T>::Impl {
public:
    boost::lockfree::queue<T> lockfree_queue;
    
    explicit Impl(size_t capacity) : lockfree_queue(capacity) {}
};

template<typename T>
Queue<T>::Queue(size_t capacity) : pImpl(std::make_unique<Impl>(capacity)) {
    // Constructor
}

template<typename T>
Queue<T>::~Queue() = default;

template<typename T>
void Queue<T>::initialize() {
    std::cout << "Thread-safe queue initialized (Boost.Lockfree backend)" << std::endl;
}

template<typename T>
bool Queue<T>::process() {
    std::cout << "Queue ready (using Boost lockfree queue)" << std::endl;
    return true;
}

template<typename T>
bool Queue<T>::push(const T& item) {
    return pImpl->lockfree_queue.push(item);
}

template<typename T>
std::optional<T> Queue<T>::pop() {
    T item;
    if (pImpl->lockfree_queue.pop(item)) {
        return item;
    }
    return std::nullopt;
}

template<typename T>
bool Queue<T>::empty() const {
    return pImpl->lockfree_queue.empty();
}

template<typename T>
size_t Queue<T>::size() const {
    // Note: Boost lockfree queue doesn't have a size() method
    // This is a limitation of lock-free data structures
    return 0; // Return 0 as we can't determine size in lock-free manner
}

// Explicit template instantiation for common types
template class Queue<int>;
template class Queue<double>;
template class Queue<long>;

} // namespace queue
