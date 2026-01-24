// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2011 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

  localparam LP = 1;

  (* attr_name1 *)
  (* attr_name1 = 1 *)
  (* attr_name1 = LP *)
  (* attr_name1 = LP + 2, attr_name2 *)
  (* attr_name1 = val1, attr_name2=1 *)

  initial $finish;

endmodule
