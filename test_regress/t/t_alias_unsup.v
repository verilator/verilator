// DESCRIPTION: Verilator: Verilog Test module for SystemVerilog 'alias'
//
// Simple bi-directional alias test.
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2013 by Jeremy Bennett.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   // Values to swap and locations for the swapped values.
   wire [31:0] x_fwd = 32'hdeadbeef;
   wire [31:0] y_fwd;
   wire [31:0] x_bwd;
   wire [31:0] y_bwd = 32'hfeedface;

   swap swap_fwd_i (.a (x_fwd),
                    .b (y_fwd));
   swap swap_bwd_i (.a (x_bwd),
                    .b (y_bwd));

   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write ("x_fwd = %x, y_fwd = %x\n", x_fwd, y_fwd);
      $write ("x_bwd = %x, y_bwd = %x\n", x_bwd, y_bwd);
`endif
      if (y_fwd != 32'hefbeadde) $stop;
      if (x_bwd == 32'hcefaedfe) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule


// Swap the byte order of two args.
module swap (
             inout wire [31:0] a,
             inout wire [31:0] b
             );

   alias {a[7:0],a[15:8],a[23:16],a[31:24]} = b;

   // Equivalent to

   // wire [31:0] a_prime;
   // wire [31:0] b_prime;

   // assign b_prime = {a[7:0],a[15:8],a[23:16],a[31:24]};
   // assign {a_prime[7:0],a_prime[15:8],a_prime[23:16],a_prime[31:24]} = b;
   // assign b = b_prime;
   // assign a = a_prime;

endmodule
