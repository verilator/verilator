// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2010 by Wilson Snyder.

module t;
   sub sub ();
endmodule

module sub;
   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule

// verilator lint_off MODDUP
module sub;
   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
