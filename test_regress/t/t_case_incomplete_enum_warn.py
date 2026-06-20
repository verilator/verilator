#!/usr/bin/env python3
import vltest_bootstrap
test.scenarios('linter')
test.lint(fails=True, expect_filename=test.golden_filename)
test.passes()