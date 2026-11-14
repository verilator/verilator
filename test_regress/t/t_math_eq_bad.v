// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2022 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

  logic [31:0] a;
  string s;
  real r;
  // verilator lint_off SHORTREAL
  shortreal sr;
  // verilator lint_on SHORTREAL

  initial begin
    a = 1234;
    if (a ==? 1.0) $stop;  // Bad
    if (a !=? 1.0) $stop;  // Bad
    if (s ==? "1") $stop;  // Bad
    if (s !=? "1") $stop;  // Bad
    if (r ==? r) $stop;  // Bad
    if (r !=? r) $stop;  // Bad
    if (sr ==? sr) $stop;  // Bad
    if (sr !=? sr) $stop;  // Bad
  end

endmodule
