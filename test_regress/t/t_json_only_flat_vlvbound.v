// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2012 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module vlvbound_test
  (
    input logic [15:0]  i_a,
    input logic [15:0]  i_b,
    output logic [6:0]  o_a,
    output logic [6:0]  o_b
  );

  function automatic logic [6:0] foo(input logic [15:0] val);
    logic [6:0] ret;
    integer i;
    for (i=0 ; i < 7; i++) begin
      ret[i] = (val[i*2 +: 2] == 2'b00);
    end
    return ret;
  endfunction

  assign o_a = foo(i_a);
  assign o_b = foo(i_b);

endmodule
