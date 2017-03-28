// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2017 by Johan Bjork.

module t ();
   simple_bus sb_intf();
   simple_bus #(.PARAMETER($bits(sb_intf.dummy))) simple();
   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule

interface simple_bus #(PARAMETER = 0);
   logic dummy;
endinterface
