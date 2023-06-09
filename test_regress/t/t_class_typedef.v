// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class uvm_resource_types;
   typedef int rsrc_q_t;
endclass

class uvm_resource_pool;
   uvm_resource_types::rsrc_q_t rtab [string];
endclass

virtual class C#(parameter type T = logic, parameter SIZE = 1);
    typedef logic [SIZE-1:0] t_vector;
    typedef T t_array [SIZE-1:0];
    typedef struct {
        t_vector m0 [2*SIZE-1:0];
        t_array m1;
    } t_struct;
endclass

module t (/*AUTOARG*/);
   initial begin
      uvm_resource_pool pool = new;
      typedef logic [7:0] t_t0;
      C#(t_t0,3)::t_vector v0;
      C#(t_t0,3)::t_array a0;
      C#(bit,4)::t_struct s0;

      pool.rtab["a"] = 1;
      if ($bits(pool.rtab["a"]) != 32) $stop;

      if ($bits(v0) != 3) $stop;
      if ($size(a0) != 3) $stop;
      if ($bits(a0[0]) != 8) $stop;
      if ($size(s0.m0) != 8) $stop;
      if ($size(s0.m1) != 4) $stop;
      if ($bits(s0.m1[2]) != 1) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
