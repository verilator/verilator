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

module no_warn#(PARAM = 1)(input in, input clk);
  typedef enum {A, B} enum_t;

  // Do not warn on variables under modules.
  logic tmp = in;

  // Do not warn on assignment with module var.
  function static func;
    static logic func_var = tmp;
  endfunction

  // Do not warn on constant assignments.
  function static func_param;
    static logic func_var = PARAM;
    static logic func_enum = A;
  endfunction

  // Do not warn on non-IO assignments.
  function static func_local;
    automatic logic loc;
    static logic func_var = loc;
  endfunction

   // Do not warn on assignment referencing module I/O.
   function static func_module_input;
     logic tmp = in;
   endfunction

   // Do not warn on automatic assignment.
   function automatic func_auto;
     input logic in;
     logic tmp = in;
   endfunction

   // Do not warn on assignment separate from declaration.
   function static func_decl_and_assign;
     input logic in;
     logic tmp;
     tmp = in;
   endfunction

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

   function automatic func_auto_with_static;
     input logic in;
     static logic tmp = in;
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
   no_warn no_warn(.in(in), .clk(clk));

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
