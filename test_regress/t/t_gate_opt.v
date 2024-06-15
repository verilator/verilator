// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Yutetsu TAKATSUKASA.
// SPDX-License-Identifier: CC0-1.0

// bug5101
module t ();

   logic [1:0] in0, in1, out;
   logic sel;
   assign in0 = 1;
   assign in1 = 2;
   assign sel = 1'b1;

   initial begin
      $display("out:%d", out);
      $write("*-* All Finished *-*\n");
      $finish;
   end

   bug5101 u_bug5101(.in0, .in1, .sel, .out);
endmodule


module bug5101(input wire [1:0] in0, input wire [1:0] in1, input wire sel, output logic [1:0] out);
   // verilator no_inline_module
   function logic [1:0] incr(input [1:0] in);
      logic [1:0] tmp;
      tmp = in + 1;
      return tmp;
  endfunction

  always_comb
     if (sel) out = in0;
     else out = incr(in1);
endmodule
