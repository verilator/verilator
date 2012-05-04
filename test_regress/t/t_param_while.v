// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012 by Wilson Snyder.

//bug505

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   parameter  WIDTH = 33;
   localparam MAX_WIDTH = 11;
   localparam NUM_OUT = num_out(WIDTH);

   wire [NUM_OUT-1:0] z;

   function integer num_out;
      input integer width;
      num_out = 1;
      while ((width + num_out - 1) / num_out > MAX_WIDTH)
        num_out = num_out * 2;
   endfunction

   initial begin
      if (NUM_OUT != 4) $stop;
      if ($bits(z) != 4) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
