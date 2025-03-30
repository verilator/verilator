// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
   Iface ifc();

   initial begin
      #1;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule

interface Iface;
  int tck;
  int tdo;

  task tsk(input int data_i, output int data_o);
     @(posedge tck);
     data_o <= tdo;
  endtask

endinterface
