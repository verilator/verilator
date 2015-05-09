// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2015 by Wilson Snyder.

module t;
   function integer bottom_4bits;
      input [7:0] i;
      bottom_4bits = 0;
      bottom_4bits[3:0] = i[3:0];
   endfunction

   function integer bottom_2_unknown;
      input [7:0] i;
      // bottom_4bits = 0;  'x
      bottom_2_unknown[1:0] = i[1:0];
   endfunction

   localparam p = bottom_4bits(8'h13);
   localparam bu = bottom_2_unknown(8'h13);

   initial begin
      if (p != 3) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
