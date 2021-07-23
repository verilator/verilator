// DESCRIPTION: Verilator: public clock signal
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2021 by Todd Strader
// SPDX-License-Identifier: CC0-1.0

module t ();

   logic clk /* verilator public_flat_rw */ = 0;
   int count;
   logic other_clk;

   sub_mod sub_mod_u (
       .sub_in(clk),
       .sub_out(other_clk)
    );

   always_ff @(posedge other_clk) begin
      count <= count + 1;
      if (count == 10) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule


module sub_mod
  (
   input  var logic sub_in,
   output var logic sub_out
   );

   always_comb sub_out = ~sub_in;

endmodule
