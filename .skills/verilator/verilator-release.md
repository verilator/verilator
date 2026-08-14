---
name: verilator-release
description: Release process - --enable-ccwarn, --enable-longtests, version bump, Changes file, tagging
---

# Verilator Release Skill

## Release Checklist (Maintainer Only)

### Pre-Release
- [ ] All CI passing on all OS (Linux, macOS, Windows)
- [ ] `make test` passes with `--enable-longtests`
- [ ] `make cppcheck` clean
- [ ] `make lint-py` clean
- [ ] No open PRs blocking release

### Version Bump
```bash
# Version in configure.ac
AC_INIT([Verilator], [5.XX.XX], ...)

# Update version in src/Verilator.cpp
static const char* versionStr = "Verilator 5.XX.XX";
```

### Changes File
```bash
# Edit Changes - maintainer writes release notes
# Format:
# Verilator 5.XX.XX (date)
#   - Feature: ...
#   - Fix: ...
```

### Build & Test
```bash
autoconf && ./configure --enable-ccwarn --enable-longtests && make -j8
make test
```

### Tag & Release
```bash
git tag -a v5.XX.XX -m "Verilator 5.XX.XX"
git push origin v5.XX.XX
```

## Configure Options Reference

| Option | Purpose | Release Default |
|--------|---------|-----------------|
| `--enable-ccwarn` | Treat compiler warnings as errors | **ON** |
| `--enable-longtests` | Run full regression suite | **ON** |
| `--enable-debug` | Build with debug symbols | OFF |
| `--enable-coverage` | Code coverage instrumentation | OFF |
| `--enable-uvm` | UVM support | ON |

## CI Configuration (maintainer)

```yaml
# .github/workflows/ci.yml
# - Runs on Linux, macOS, Windows
# - Tests: make test (with --enable-longtests on Linux)
# - Checks: cppcheck, lint-py, format
```

## Token Efficiency

- This skill is for maintainers only
- Agents building from source: use `--enable-ccwarn`
- Full test suite: `--enable-longtests` (required for PR submission)