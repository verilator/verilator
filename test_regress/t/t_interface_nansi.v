// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Geza Lore.
// SPDX-License-Identifier: CC0-1.0

interface iface(input logic clk);
   logic [31:0] d = 0;
   logic [31:0] q = 0;
endinterface

module mod(a);
   iface a; // This is not a CELL, it is a port declaration
   always @(posedge a.clk) a.q <= a.d;
endmodule

module t(clk);
   input clk;

   iface iface_inst(clk);
   mod   mod_inst(iface_inst);

   int   cyc = 0;

   always @(posedge clk) begin
      iface_inst.d <= cyc;
      if (cyc > 1 && iface_inst.q != cyc - 2) $stop;
   end

   always @(posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 100) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
