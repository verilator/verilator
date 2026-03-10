// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
module t;
  `define RECURSE `RECURSE
  `RECURSE

  initial $stop;  // Should have failed

endmodule
