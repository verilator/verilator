// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2016 by Adrian Wise.
// SPDX-License-Identifier: CC0-1.0

//bug1246

module t(input clk);
   my_interface iface();
   my_module m(.clk(clk), iface);
endmodule

module my_module(input clk, my_interface.my_port iface);
   always @(posedge clk) begin
      iface.b <= iface.a;
      iface.c <= iface.a;
   end
endmodule

interface my_interface;
   logic a, b, c;
   modport my_port(input a, output b, c);
endinterface
