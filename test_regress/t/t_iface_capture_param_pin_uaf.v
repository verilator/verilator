// DESCRIPTION: Verilator: interface typedef capture use-after-free (issue #8492)
//
// The parameter assignment `.rq_pt(types.rq_t)` is freed once `u` is
// deparameterized; the second `mid` specialization must not read it again.
// This was a heap-use-after-free, caught by --enable-dev-asan builds.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

interface tif #(parameter int N = 8)();
  typedef logic [N-1:0] rq_t;
endinterface

module child #(parameter type rq_pt = logic)();
endmodule

module mid #(parameter int P = 0)();
  tif #(.N(16)) types();
  child #(.rq_pt(types.rq_t)) u();
endmodule

module top;
  mid #(.P(1)) u();
  mid #(.P(2)) u2();
endmodule
