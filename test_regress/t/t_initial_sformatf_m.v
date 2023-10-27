// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Todd Strader.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   sub_t some_sub_module(.clk);
endmodule

module sub_t (
   input clk
);
   localparam string NAME = $sformatf("%m");

   always @(posedge clk) begin
      if (NAME != "t.some_sub_module") begin
         $display("%%Error: NAME = %s", NAME);
         $stop;
      end
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
