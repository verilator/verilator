// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Parse check
class uvm_resource_types;
   typedef int rsrc_q_t;
endclass
class uvm_resource_pool;
   uvm_resource_types::rsrc_q_t rtab [string];

   uvm_resource_types#(1,2,3)::rsrc_q_t rtab_paramed [string];
endclass

module t (/*AUTOARG*/);
   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
