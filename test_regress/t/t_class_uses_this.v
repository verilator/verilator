// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 Rafal Kapuscik
// SPDX-License-Identifier: CC0-1.0
//
class Cls;
   bit [3:0] addr;
   function void set(bit [3:0] addr);
   begin : body
     this.addr = addr;
   end : body
   endfunction
   function void set2(bit [3:0] addr);
   begin : body
     Cls c2 = this;
     c2.addr = addr;
   end : body
   endfunction
   extern function void setext(bit [3:0] addr);
   extern function void setext2(bit [3:0] addr);
endclass

function void Cls::setext(bit [3:0] addr);
   this.addr = addr;
endfunction

function void Cls::setext2(bit [3:0] addr);
   Cls c2 = this;
   c2.addr = addr;
endfunction

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;
   Cls bar;
   Cls baz;
   initial begin
      bar = new();
      baz = new();
      bar.set(4);
`ifdef TEST_VERBOSE
      $display(bar.addr);
      $display(baz.addr);
`endif
      if (bar.addr != 4) $stop;
      bar.set2(1);
      if (bar.addr != 1) $stop;
      bar.setext(2);
      if (bar.addr != 2) $stop;
      bar.setext2(3);
      if (bar.addr != 3) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
