#!/bin/bash
# Pre-commit hook for validating design patterns
# Install with: ln -s ../../scripts/pre-commit-hook.sh .git/hooks/pre-commit

set -e

echo "Running design pattern validation..."

# Run the validator
python3 scripts/validate_design_patterns.py

if [ $? -ne 0 ]; then
    echo ""
    echo "❌ Design pattern validation failed!"
    echo "Please fix the issues above before committing."
    echo ""
    echo "To bypass this check (not recommended), use: git commit --no-verify"
    exit 1
fi

echo "✅ Design pattern validation passed!"
exit 0
