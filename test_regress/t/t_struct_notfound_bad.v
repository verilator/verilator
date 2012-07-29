// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012 by Wilson Snyder.

module t (/*AUTOARG*/);

   typedef struct packed { bit m; } struct_t;
   struct_t s;

   initial begin
      s.nfmember = 0; // Member not found
      $finish;
   end
endmodule
