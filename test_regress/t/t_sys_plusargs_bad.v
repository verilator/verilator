// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2009 by Wilson Snyder.

module t;

   integer p_i;

   initial begin
      // BAD: Missing argument
      if ($value$plusargs("NOTTHERE", p_i)!==0) $stop;

      // BAD: Bad letter
      if ($value$plusargs("INT=%z", p_i)!==0) $stop;

      // BAD: Multi letter
      if ($value$plusargs("INT=%x%x", p_i)!==0) $stop;

      $stop;
   end
endmodule
