// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

interface Bus;
   logic [7:0] data;
endinterface

class Cls;
   virtual Bus vbus;

   function void check(logic [7:0] data);
       if (vbus.data != data) $stop;
   endfunction
endclass

module t (clk);
   input clk;
   int cyc = 0;

   Bus bus();
   virtual Bus vbus;
   Cls obj;

   assign bus.data = 'hFA;

   always @(posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 1) begin
         obj = new;
         vbus = bus;
         obj.vbus = bus;
      end
      else if (cyc == 2) begin
         obj.check('hFA);
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
