#ifndef EMAIL_VALIDATOR_H
#define EMAIL_VALIDATOR_H

namespace email_validator {

class EmailValidator {
public:
    EmailValidator();
    ~EmailValidator();
    
    void initialize();
    bool process();
};

} // namespace email_validator

#endif // EMAIL_VALIDATOR_H
