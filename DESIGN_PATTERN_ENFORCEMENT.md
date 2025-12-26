# Design Pattern Enforcement Tooling

This document explains the tooling available to enforce design patterns and architectural conventions in the DIY Conan Center repository.

## Overview

The design pattern enforcement system consists of:

1. **Validation Script** - Automated checker for design patterns
2. **GitHub Actions Integration** - CI/CD validation
3. **Pre-commit Hook** - Local validation before commits
4. **Configuration File** - Customizable validation rules

## Validation Script

### Location
`scripts/validate_design_patterns.py`

### Usage

```bash
# Validate all packages
python3 scripts/validate_design_patterns.py

# Run from any directory
cd /path/to/diyconancenter
python3 scripts/validate_design_patterns.py
```

### What It Checks

#### 1. Naming Conventions
- ✅ Package names are kebab-case (e.g., `json-parser`)
- ✅ Domain-specific packages use appropriate prefixes
  - `game-*` for game development
  - `web-*` for web development
  - `cad-*` for CAD/3D modeling
  - `print-*` for 3D printing
  - `ml-*` or `ai-*` for AI/ML
  - `dev-*` for development tools
  - `server-*` for server infrastructure

#### 2. Package Structure
- ✅ Required files exist (`conanfile.py`, `CMakeLists.txt`)
- ✅ Proper directory structure (`src/`, `include/`, `test_package/`)
- ✅ Header and source files follow conventions

#### 3. Conanfile Requirements
- ✅ Required attributes present (`name`, `version`, `license`)
- ✅ Proper imports (e.g., `import os` when using `os` module)
- ✅ Settings defined for compiled libraries

#### 4. Code Quality
- ✅ Header guards follow conventions
- ✅ Namespaces match package names
- ✅ Smart pointers used instead of raw pointers (Pimpl pattern)
- ✅ CMake follows best practices

#### 5. Testing
- ✅ Test package exists and is complete
- ✅ Test files properly structured

### Output Example

```
======================================================================
DIY CONAN CENTER - DESIGN PATTERN VALIDATOR
======================================================================
Repository: /path/to/diyconancenter

Found 50 packages to validate
Validating json-parser...
Validating logger...
...

======================================================================
VALIDATION SUMMARY
======================================================================
Errors:   0
Warnings: 5
Info:     2
======================================================================

Issues found:

  [ERROR] bad-package: naming - Package name should be kebab-case
  [WARNING] http-server: naming - Should use 'web-' prefix
  [INFO] some-lib: headers - Consider using namespace 'some_lib'

✅ All packages passed validation!
```

### Exit Codes

- `0` - All checks passed (warnings are acceptable)
- `1` - One or more errors found

## GitHub Actions Integration

### Workflow File
`.github/workflows/build-packages.yml`

### How It Works

The validation runs as a separate job **before** building packages:

```yaml
jobs:
  validate-design-patterns:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-python@v5
      - run: python3 scripts/validate_design_patterns.py

  build-packages:
    needs: validate-design-patterns  # Waits for validation
    ...
```

### When It Runs

- ✅ On every push to `main` or `master`
- ✅ On every pull request
- ✅ On manual workflow dispatch
- ✅ Before building/testing packages

### Viewing Results

1. Go to GitHub Actions tab in your repository
2. Click on the workflow run
3. View the "validate-design-patterns" job
4. See detailed validation output

### Handling Failures

If validation fails:
1. Review the error messages in the GitHub Actions log
2. Fix the issues locally
3. Run `python3 scripts/validate_design_patterns.py` to verify
4. Commit and push the fixes

## Pre-commit Hook

### Installation

```bash
# From repository root
ln -s ../../scripts/pre-commit-hook.sh .git/hooks/pre-commit
chmod +x .git/hooks/pre-commit
```

### What It Does

- Runs validation before every `git commit`
- Blocks commits if errors are found
- Provides immediate feedback

### Bypassing (Not Recommended)

```bash
# Skip validation for a single commit
git commit --no-verify -m "Emergency fix"
```

**Warning:** Only use `--no-verify` in emergencies. The CI will still catch issues.

## Configuration File

### Location
`.design-patterns.yml`

### Structure

```yaml
rules:
  naming:
    kebab_case: "error"        # Severity: error, warning, info, disabled
    domain_prefix: "warning"
  
  structure:
    require_conanfile: "error"
    require_test_package: "warning"

domain_prefixes:
  - "game-"
  - "web-"
  - "cad-"

exemptions:
  legacy_packages:
    - "old-package"  # Exempt from all rules
```

### Severity Levels

| Level | Meaning | Exit Code |
|-------|---------|-----------|
| `error` | Must be fixed | Non-zero |
| `warning` | Should be fixed | Zero (passes) |
| `info` | Informational only | Zero (passes) |
| `disabled` | Rule not checked | Zero (passes) |

### Customizing Rules

Edit `.design-patterns.yml` to:
- Change severity levels
- Add domain prefixes
- Add domain keywords
- Exempt specific packages

Example:
```yaml
rules:
  naming:
    domain_prefix: "disabled"  # Disable domain prefix warnings

exemptions:
  custom_rules:
    my-special-package:
      - "naming.domain_prefix"  # Exempt just this package
```

## Best Practices

### For Package Authors

1. **Run validator before committing**
   ```bash
   python3 scripts/validate_design_patterns.py
   ```

2. **Install pre-commit hook**
   ```bash
   ln -s ../../scripts/pre-commit-hook.sh .git/hooks/pre-commit
   ```

3. **Address errors immediately**
   - Errors block CI/CD
   - Fix before pushing

4. **Consider warnings seriously**
   - Warnings improve consistency
   - Fix when possible

### For Maintainers

1. **Review validation output in PRs**
   - Check GitHub Actions tab
   - Ensure patterns are followed

2. **Update configuration as needed**
   - Edit `.design-patterns.yml`
   - Document changes

3. **Keep validator up to date**
   - Add new rules as patterns evolve
   - Update documentation

## Common Issues and Solutions

### Issue: "Package name should be kebab-case"
**Solution:** Rename package to use lowercase with hyphens
```
Bad:  JsonParser, json_parser
Good: json-parser
```

### Issue: "Domain-specific package should use prefix"
**Solution:** Add appropriate domain prefix
```
Bad:  http-server, physics-engine
Good: web-http-server, game-physics-engine
```

### Issue: "Missing 'settings' attribute"
**Solution:** Add settings to conanfile.py
```python
class MyPackageConan(ConanFile):
    settings = "os", "compiler", "build_type", "arch"
```

### Issue: "Uses 'os' module but doesn't import it"
**Solution:** Add import at top of conanfile.py
```python
import os
from conan import ConanFile
```

### Issue: "Use std::unique_ptr instead of raw pointer"
**Solution:** Replace raw pointer with smart pointer
```cpp
// Bad
class Impl;
Impl* pImpl;

// Good
class Impl;
std::unique_ptr<Impl> pImpl;
```

## Extending the Validator

### Adding New Rules

1. Edit `scripts/validate_design_patterns.py`
2. Add validation method to `DesignPatternValidator` class
3. Call method from `validate_package()`
4. Update `.design-patterns.yml` with new rule
5. Document in this file

Example:
```python
def check_new_rule(self, package_name: str, version_dir: Path):
    """Validate new rule."""
    # Check something
    if condition:
        self.errors.append(ValidationError(
            "warning", package_name, "new_rule",
            "Issue description"
        ))
```

### Adding New Domain

1. Edit `.design-patterns.yml`
2. Add domain prefix to `domain_prefixes`
3. Add keywords to `domain_keywords`
4. Update `ARCHITECTURAL_PATTERNS.md`

Example:
```yaml
domain_prefixes:
  - "robotics-"

domain_keywords:
  robotics:
    - "robot"
    - "sensor"
    - "actuator"
```

## Troubleshooting

### Validator Not Running in CI

1. Check workflow file syntax
2. Ensure Python is set up correctly
3. Verify script path is correct

### Validation Passes Locally but Fails in CI

1. Check for environment differences
2. Ensure all files are committed
3. Check Python version compatibility

### Too Many Warnings

1. Review `.design-patterns.yml`
2. Adjust severity levels
3. Add exemptions if needed
4. Or fix the warnings!

## References

- [ARCHITECTURAL_PATTERNS.md](ARCHITECTURAL_PATTERNS.md) - Design patterns documentation
- [README.md](README.md) - Coding style and conventions
- [DOCUMENTATION.md](docs/DOCUMENTATION.md) - General documentation

## Support

For issues or questions:
1. Check this documentation
2. Review existing package examples
3. Open an issue on GitHub
