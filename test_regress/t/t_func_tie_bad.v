// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2011 by Wilson Snyder.

module t (/*AUTOARG*/);

   initial begin
      func(0, 1'b1);
   end

   function automatic int func
     (
      input int a,
      output bit b );
      return 0;
   endfunction

endmodule
