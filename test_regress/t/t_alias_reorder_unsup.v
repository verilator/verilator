// DESCRIPTION: Verilator: Verilog Test module for SystemVerilog 'alias'
//
// Simple bi-directional reorder alias test.
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk);

   input clk;

   wire [31:0] a = 32'hdeadbeef;
   wire [31:0] b;
   wire [31:0] c;
   wire [31:0] d = 32'hfeedface;

   reorder reorder_a_i (.a (a), .b (b));
   reorder reorder_d_i (.a (c), .b (d));

   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write ("a = %x, b = %x\n", a, b);
      $write ("c = %x, d = %x\n", c, d);
`endif
      if (b != 32'hefbeadde) $stop;
      if (c != 32'hcefaedfe) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule

module reorder (
   inout wire [31:0] a,
   inout wire [31:0] b);

   alias {a[7:0],a[15:8],a[23:16],a[31:24]} = b;

endmodule
