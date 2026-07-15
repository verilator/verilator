// DESCRIPTION: Verilator: Hierarchical finish-capability propagation
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);
  NoFinish no_finish (.clk(clk));
  EvalFinish eval_finish (.clk(clk));
  FinalFinish final_finish ();
  MiddleFinish middle_finish (.clk(clk));
  UnusedClassFinish unused_class_finish ();
  EvalClassFinish eval_class_finish ();
  FinalClassFinish final_class_finish ();
  AliasedCanonicalWrapper aliased_canonical_wrapper ();
  AliasedNearMissWrapper aliased_near_miss_wrapper ();

  int final_cycles;
  always @(posedge clk) begin
    final_cycles++;
    if (($test$plusargs("FINAL") || $test$plusargs("CLASS_FINAL")) && final_cycles == 4) begin
      $finish;
    end
  end
endmodule

module NoFinish (
    input clk
);  /*verilator hier_block*/
  int cycles;
  always @(posedge clk) cycles++;
endmodule

module EvalFinish (
    input clk
);  /*verilator hier_block*/
  int cycles;
  always @(posedge clk) begin
    cycles++;
    if ($test$plusargs("EVAL") && cycles == 2) begin
      $write("EVAL_FINISH_EXECUTED\n");
      $write("*-* All Finished *-*\n");
      $finish;
      $stop;
    end
  end
endmodule

module FinalFinish;  /*verilator hier_block*/
  final begin
    if ($test$plusargs("FINAL")) begin
      $write("FINAL_FINISH_EXECUTED\n");
      $write("*-* All Finished *-*\n");
      $finish;
      $stop;
    end
  end
endmodule

module MiddleFinish (
    input clk
);  /*verilator hier_block*/
  LeafFinish leaf_finish (.clk(clk));
endmodule

module LeafFinish (
    input clk
);  /*verilator hier_block*/
  int cycles;
  always @(posedge clk) begin
    cycles++;
    if ($test$plusargs("NESTED") && cycles == 3) begin
      $write("NESTED_FINISH_EXECUTED\n");
      $finish;
      $stop;
    end
  end
endmodule

module UnusedClassFinish;  /*verilator hier_block*/
  class FinishObject;
    int value = finish_initializer();

    function automatic int finish_initializer();
      $finish;
      $stop;
      return 1;
    endfunction
  endclass

  FinishObject object;
endmodule

module EvalClassFinish;  /*verilator hier_block*/
  class FinishObject;
    int value = finish_initializer();

    function automatic int finish_initializer();
      $write("CLASS_EVAL_FINISH_EXECUTED\n");
      $write("*-* All Finished *-*\n");
      $finish;
      $stop;
      return 1;
    endfunction
  endclass

  FinishObject object;
  initial if ($test$plusargs("CLASS_EVAL")) object = new;
endmodule

module FinalClassFinish;  /*verilator hier_block*/
  class FinishObject;
    int value = finish_initializer();

    function automatic int finish_initializer();
      $write("CLASS_FINAL_FINISH_EXECUTED\n");
      $write("*-* All Finished *-*\n");
      $finish;
      $stop;
      return 1;
    endfunction
  endclass

  FinishObject object;
  final if ($test$plusargs("CLASS_FINAL")) object = new;
endmodule

// Models generated hierarchy wrappers whose SV and canonical C DPI names differ.
module AliasedCanonicalWrapper;
  import "DPI-C" aliased_canonical_c = function void aliased_canonical_sv();
  initial aliased_canonical_sv();
endmodule

module AliasedNearMissWrapper;
  import "DPI-C" aliased_near_miss_c = function void aliased_near_miss_sv();
  initial aliased_near_miss_sv();
endmodule
