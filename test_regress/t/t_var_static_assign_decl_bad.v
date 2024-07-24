// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

function static func_stat;
  input logic in;
  logic tmp = in;
endfunction

task static task_stat;
  input logic in;
  logic tmp = in;
endtask

package pkg;
   function static func_stat;
     input logic in;
     logic tmp = in;
   endfunction

   task static task_stat;
     input logic in;
     logic tmp = in;
   endtask
endpackage

interface iface;
   function static func_stat;
     input logic in;
     logic tmp = in;
   endfunction

   task static task_stat;
     input logic in;
     logic tmp = in;
   endtask
endinterface

program prog;
   function static func_stat;
     input logic in;
     logic tmp = in;
   endfunction

   task static task_stat;
     input logic in;
     logic tmp = in;
   endtask
endprogram

module mod(input in, input clk);
  // Do not warn on variables under modules.
  logic tmp = in;

  // Do not warn on variables under blocks.
  initial begin
    logic init_tmp = in;
  end

  always @(posedge clk) begin
    logic always_tmp = in;
  end
endmodule

module t(input clk);
   function static func_stat;
     input logic in;
     logic tmp = in;
   endfunction

   task static task_stat;
     input logic in;
     logic tmp = in;
   endtask

   function automatic func_auto;
     input logic in;
     // Do not warn on automatic assignment.
     logic tmp = in;
   endfunction

   function automatic func_auto_with_static;
     input logic in;
     static logic tmp = in;
   endfunction

   function static func_decl_and_assign;
     input logic in;
     logic tmp;
     // Do not warn on assignment separate from declaration.
     tmp = in;
   endfunction

   function static func_assign_out;
     output logic out;
     logic tmp = out;
   endfunction

   function static func_assign_expr;
     input logic in;
     logic tmp = in + 1;
   endfunction

   function static func_module_input;
     // Do not warn on assignment referencing module I/O.
     logic tmp = clk;
   endfunction

   iface iface();
   prog prog;

   logic in;
   mod mod(.in(in), .clk(clk));

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
