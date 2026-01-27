// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t;
  real r;
  bit b;

  initial begin
    r = 1492.4;
    `checkh(r inside {[1492 +/- 2]}, 1'b1);
    `checkh(r inside {[1482 +/- 2]}, 1'b0);
    `checkh(r inside {[1490 +%- 10]}, 1'b1);
    `checkh(r inside {[1090 +%- 10]}, 1'b0);
  end

endmodule
