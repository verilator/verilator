# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import math
import re

# Jensen-Shannon divergence (JSD) measures how far the "shape" of the
# observed distribution is from perfectly uniform.
# 0 means identical to uniform; it grows as the observed
# distribution gets more skewed. Scaled here x100, to notice differences easier
JSD_MAX = 2.5


def jensen_shannon_divergence_pct(observed_counts, solutions):
    n_obs = sum(observed_counts.values())
    p = [1.0 / len(solutions) for _ in solutions]  # uniform
    q = [observed_counts.get(s, 0) / n_obs for s in solutions]  # observed
    m = [(pi + qi) / 2 for pi, qi in zip(p, q)]

    def kl(a, b):
        return sum(ai * math.log(ai / bi) for ai, bi in zip(a, b) if ai > 0)

    return (kl(p, m) + kl(q, m)) / 2 * 100


def run(test, solutions, line_pattern, key=lambda line: line):
    """Check that randomize() samples `solutions` close enough to uniformly.

    line_pattern picks out the run-log lines carrying a sample, and key turns
    such a line into the value used to look it up in `solutions`.
    """
    if not test.have_solver:
        test.skip("No constraint solver installed")

    test.compile()

    test.execute()

    observed = {}
    with open(test.run_log_filename, 'r', encoding='latin-1') as fh:
        for line in fh:
            line = line.strip()
            if re.fullmatch(line_pattern, line):
                value = key(line)
                observed[value] = observed.get(value, 0) + 1

    jsd = jensen_shannon_divergence_pct(observed, solutions)
    if jsd > JSD_MAX:
        test.error("JSD %.6f exceeds max %.6f -- distribution is not uniform enough" %
                   (jsd, JSD_MAX))

    test.passes()
