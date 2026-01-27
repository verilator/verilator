// DESCRIPTION: Verilator: Verilog Test module
//
// A test that a package import declaration can precede a parameter port list
// in an interface declaration. See IEEE 1800-2023 25.3.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2013 Jeremy Bennett
// SPDX-License-Identifier: CC0-1.0

package bus_pkg;
  parameter WIDTH = 8;
endpackage

interface simple_bus
  import bus_pkg::*; // Import preceding parameters.
  #(p_width = WIDTH)
   (input logic clk);

   logic req, gnt;
   logic [p_width-1:0] addr;
   logic [p_width-1:0] data;

   modport slave(input req, addr, clk,
                 output gnt,
                 input  data);

   modport master(input gnt, clk,
                  output req, addr,
                  output data);

endinterface

module mem(simple_bus a);
   logic avail;
   always @(posedge a.clk)
     a.gnt <= a.req & avail;
   initial begin
      if ($bits(a.data) != 8) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule

module t (input clk);
   simple_bus sb(clk);
   mem mem(sb.slave);
endmodule
