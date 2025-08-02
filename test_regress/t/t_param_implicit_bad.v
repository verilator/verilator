// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// IEEE parameter_port_declaration has data_type but not data_type_or_implicit

module sub1 #([7:0] PAR1 = 1);  // <--- Error: requires 'parameter'
endmodule

module sub2 #(parameter real PAR1 = 1.0, signed PAR2 = 2);
endmodule

module sub3 #(localparam real PAR1 = 1.0, signed PAR2 = 2);
endmodule

module t;
  sub1 sub1();
  sub2 sub2();
  sub3 sub3();
  initial $stop;
endmodule
