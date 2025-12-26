#ifndef TEMPLATE_ENGINE_H
#define TEMPLATE_ENGINE_H

namespace template_engine {

class TemplateEngine {
public:
    TemplateEngine();
    ~TemplateEngine();
    
    void initialize();
    bool process();
};

} // namespace template_engine

#endif // TEMPLATE_ENGINE_H
