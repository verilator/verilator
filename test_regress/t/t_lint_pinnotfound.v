// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

/* verilator lint_off PINNOTFOUND */
module a;
localparam A=1;
generate
if (A==0)
begin
b b_inst1 (.x(1'b0)); // nonexistent port
b #(.PX(1'b0)) b_inst2 (); // nonexistent parameter
end
endgenerate
endmodule

module b;
endmodule
