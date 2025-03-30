// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
   Iface ifc();
   rvlab_tests uut (.ifc);

   always begin
      uut.test_idcode();
   end
   initial begin
      #1;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule

interface Iface;
  logic tck;
  logic tdo;

  task tsk(output logic [31:0] data_o, input logic [31:0] data_i);
     @(posedge tck);
     data_o[$size(data_i)-1] <= tdo;
  endtask
endinterface

module rvlab_tests (
   Iface ifc);
   task test_idcode();
      bit [31:0] idcode_read;
      ifc.tsk(idcode_read, '0);
   endtask
endmodule
