// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2016 by Adrian Wise.
// SPDX-License-Identifier: CC0-1.0

//bug1104

module t (input clk);
   simple_bus sb_intf(clk);
   simple_bus #(.DWIDTH(16)) wide_intf(clk);
   mem mem(sb_intf.slave);
   cpu cpu(sb_intf.master);
   mem memW(wide_intf.slave);
   cpu cpuW(wide_intf.master);
endmodule

interface simple_bus #(AWIDTH = 8, DWIDTH = 8)
   (input logic clk);  // Define the interface

   logic req, gnt;
   logic [AWIDTH-1:0] addr;
   logic [DWIDTH-1:0] data;

   modport slave( input req, addr, clk,
                  output gnt,
                  input  data);

   modport master(input gnt, clk,
                  output req, addr,
                  output data);

   initial begin
      if (DWIDTH != 16) $stop;
   end
endinterface: simple_bus

module mem(interface a);
   logic avail;
   always @(posedge a.clk)
     a.gnt <= a.req & avail;
   initial begin
      if ($bits(a.data) != 16) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule

module cpu(interface b);
endmodule
