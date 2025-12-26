#include "email_validator.h"
#include <iostream>

namespace email_validator {

EmailValidator::EmailValidator() {
    // Constructor
}

EmailValidator::~EmailValidator() {
    // Destructor
}

void EmailValidator::initialize() {
    std::cout << "Initializing email-validator..." << std::endl;
}

bool EmailValidator::process() {
    std::cout << "Processing with email-validator..." << std::endl;
    return true;
}

} // namespace email_validator
