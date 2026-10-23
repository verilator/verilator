// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module chk (
    input clk
);
endmodule

module sub (
    input clk
);
endmodule

module t (
    input clk
);
  sub u_sub (.clk);
  // Bad: no module or interface named 'no_such_module'
  bind no_such_module chk u_chk1 (.clk);
  // Good
  bind sub chk u_chk2 (.clk);
endmodule
