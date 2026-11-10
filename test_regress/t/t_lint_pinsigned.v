// DESCRIPTION: Verilator: Test signed input port literal warning
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  typedef logic signed [13:0] coeff_t;
  sink a(.coeff(14'd10483));
  sink b(14'd8192);
  sink c(14'd8191);
  sink d(14'sd8192);
  sink e($signed(14'd10483));
  sink f(coeff_t'(14'd10483));
  sink g(14'b1x000000000000);
  sink h(14'bx0000000000000);
  sink i(14'd0);
  sink j('1);
  // verilator lint_off WIDTHTRUNC
  sink k(32'd10483);
  // verilator lint_on WIDTHTRUNC
  sink_unsigned l(14'd10483);
  sink_wide m(96'h800000000000000000000000);
  sink_wide n(96'h7fffffffffffffffffffffff);
  sink_bit p(1'b1);
  sink_bit q(1'b0);
  sink_bit r('1);
  // verilator lint_off PINSIGNED
  sink o(14'd10483);
  // verilator lint_on PINSIGNED
endmodule

module sink(input signed [13:0] coeff);
endmodule
module sink_unsigned(input [13:0] coeff);
endmodule
module sink_wide(input signed [95:0] coeff);
endmodule

module sink_bit(input signed coeff);
endmodule
