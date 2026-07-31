#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import math
import re

import vltest_bootstrap

test.scenarios('simulator')

if not test.have_solver:
    test.skip("No constraint solver installed")

test.compile()

test.execute()

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


SOLUTIONS = [i for i in range(256) if bin(i).count('1') == 4]  # C(8,4) = 70

observed = {}
with open(test.run_log_filename, 'r', encoding='latin-1') as fh:
    for line in fh:
        line = line.strip()
        if re.fullmatch(r'\d+', line):
            value = int(line)
            observed[value] = observed.get(value, 0) + 1

jsd = jensen_shannon_divergence_pct(observed, SOLUTIONS)
if jsd > JSD_MAX:
    test.error("JSD %.6f exceeds max %.6f -- distribution is not uniform enough" % (jsd, JSD_MAX))

test.passes()
