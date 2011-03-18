// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2011 by Wilson Snyder.

module t;

   typedef logic [3:0] mc_t;
   typedef mc_t tocast_t;

   mc_t o;

   initial begin
      if (4'shf > 4'sh0) $stop;
      if (signed'(4'hf) > 4'sh0) $stop;
      if (4'hf < 4'h0) $stop;
      if (unsigned'(4'shf) < 4'h0) $stop;

      o = tocast_t'(4'b1);
      if (o != 4'b1) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
