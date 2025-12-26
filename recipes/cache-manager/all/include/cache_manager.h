#ifndef CACHE_MANAGER_H
#define CACHE_MANAGER_H

namespace cache_manager {

class CacheManager {
public:
    CacheManager();
    ~CacheManager();
    
    void initialize();
    bool process();
};

} // namespace cache_manager

#endif // CACHE_MANAGER_H
