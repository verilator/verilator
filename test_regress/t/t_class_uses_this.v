// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 Rafal Kapuscik
// SPDX-License-Identifier: CC0-1.0
//
class foo;
   bit [3:0] addr;
   function void set (bit [3:0] addr);
   begin : body
     this.addr = addr;
   end : body
   endfunction
endclass

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;
   foo bar;
   foo baz;
   initial begin
       bar = new();
       baz = new();
       bar.set(4);
`ifdef TEST_VERBOSE
       $display(bar.addr);
       $display(baz.addr);
`endif
       $write("*-* All Finished *-*\n");
       $finish;
   end
endmodule
