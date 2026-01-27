// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2011 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input i
);
  // verilator lint_off MODMISSING
  foobar sub (i);
endmodule
