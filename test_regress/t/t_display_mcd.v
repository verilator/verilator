// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2015 by Wilson Snyder.

module t;
   initial begin
      $fwrite(32'h8000_0001, "To stdout\n");
      $fflush(32'h8000_0001);
      $fwrite(32'h8000_0002, "To stderr\n");
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
