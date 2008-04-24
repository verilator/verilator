// $Id$
// DESCRIPTION: Verilator: Verilog Test module

module t;
   initial begin
`ifndef GOT_DEF1
      $write("%%Error: NO GOT_DEF1\n"); $stop;
`endif
`ifndef GOT_DEF2
      $write("%%Error: NO GOT_DEF2\n"); $stop;
`endif
`ifdef NON_DEF
      $write("%%Error: NON_DEF\n"); $stop;
`endif
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
