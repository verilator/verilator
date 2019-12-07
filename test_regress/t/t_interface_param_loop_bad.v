// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2019 by Johan Bjork.

module t ();
   simple_bus #(.WIDTH(simple.get_width()))  sb_intf();
   simple_bus #(.WIDTH(sb_intf.get_width())) simple();

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule

interface simple_bus #(parameter int WIDTH = 8);
   logic [WIDTH-1:0] data;

   function automatic int get_width();
      return WIDTH;
   endfunction
endinterface
