// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

`define DISPLAY_PASS(file, line) \
   $display("Passed '%m' at %s:%g", file, line)

`define DISPLAY_FAIL(file, line) \
   $display("Failed '%m' at %s:%g", file, line)

`define RUN_ALL_ASSERTS \
   $display("==========\nRunning all asserts at: %s:%g\n==========", `__FILE__, `__LINE__); \
   run_all_asserts(`__FILE__, `__LINE__); \
   cover_simple_immediate_`__LINE__: cover(1); \
   cover_simple_immediate_stmt_`__LINE__: cover(1) `DISPLAY_PASS(`__FILE__, `__LINE__); \
   cover_observed_deferred_immediate_`__LINE__: cover #0 (1); \
   cover_observed_deferred_immediate_stmt_`__LINE__: cover #0 (1) `DISPLAY_PASS(`__FILE__, `__LINE__); \
   cover_final_deferred_immediate_`__LINE__: cover final (1); \
   cover_final_deferred_immediate_stmt_`__LINE__: cover final (1) `DISPLAY_PASS(`__FILE__, `__LINE__); \

module t (/*AUTOARG*/
   clk
   );
   input clk;

   let ON = 3;
   let OFF = 4;
   let KILL = 5;

   let CONCURRENT = 1;
   let SIMPLE_IMMEDIATE = 2;
   let OBSERVED_DEFERRED_IMMEDIATE = 4;
   let FINAL_DEFERRED_IMMEDIATE = 8;

   let ALL_TYPES = CONCURRENT|SIMPLE_IMMEDIATE|OBSERVED_DEFERRED_IMMEDIATE|FINAL_DEFERRED_IMMEDIATE;

   let ASSERT = 1;
   let COVER = 2;
   let ASSUME = 4;

   concurrent concurrent(.clk(clk));

   initial begin
      // simple immediate
      $assertcontrol(OFF, ALL_TYPES);
      $assertcontrol(ON, SIMPLE_IMMEDIATE);
      `RUN_ALL_ASSERTS
      $assertcontrol(OFF, SIMPLE_IMMEDIATE);
      `RUN_ALL_ASSERTS

      // observed deferred immediate
      $assertcontrol(OFF, ALL_TYPES);
      $assertcontrol(ON, OBSERVED_DEFERRED_IMMEDIATE);
      `RUN_ALL_ASSERTS
      $assertcontrol(OFF, OBSERVED_DEFERRED_IMMEDIATE);
      `RUN_ALL_ASSERTS

      // final deferred immediate
      $assertcontrol(OFF, ALL_TYPES);
      $assertcontrol(ON, FINAL_DEFERRED_IMMEDIATE);
      `RUN_ALL_ASSERTS
      $assertcontrol(OFF, FINAL_DEFERRED_IMMEDIATE);
      `RUN_ALL_ASSERTS

      // on, off, kill test
      $assertoff;
      `RUN_ALL_ASSERTS;
      $asserton;
      `RUN_ALL_ASSERTS;
      $assertkill;
      `RUN_ALL_ASSERTS;

      $assertcontrol(ON, SIMPLE_IMMEDIATE|OBSERVED_DEFERRED_IMMEDIATE);
      `RUN_ALL_ASSERTS;
      $assertcontrol(ON, FINAL_DEFERRED_IMMEDIATE);
      `RUN_ALL_ASSERTS;
      $assertcontrol(OFF, OBSERVED_DEFERRED_IMMEDIATE|FINAL_DEFERRED_IMMEDIATE);
      `RUN_ALL_ASSERTS;
      $assertcontrol(OFF, FINAL_DEFERRED_IMMEDIATE);
      `RUN_ALL_ASSERTS;
      $assertcontrol(OFF, SIMPLE_IMMEDIATE);
      `RUN_ALL_ASSERTS;
      $assertcontrol(ON, SIMPLE_IMMEDIATE);
      `RUN_ALL_ASSERTS;
      $assertcontrol(OFF, ALL_TYPES);
      `RUN_ALL_ASSERTS;
      $assertcontrol(ON, ALL_TYPES);
      `RUN_ALL_ASSERTS;
      $assertcontrol(KILL, ALL_TYPES);
      `RUN_ALL_ASSERTS;

      // directive_type test
      $assertoff;
      $assertcontrol(ON, ALL_TYPES, ASSERT);
      `RUN_ALL_ASSERTS;
      $assertcontrol(OFF, ALL_TYPES, ASSERT);
      $assertcontrol(ON, ALL_TYPES, COVER);
      `RUN_ALL_ASSERTS;
      $assertcontrol(OFF, ALL_TYPES, COVER);
      $assertcontrol(ON, ALL_TYPES, ASSUME);
      `RUN_ALL_ASSERTS;
      $assertcontrol(OFF, ALL_TYPES, ASSUME);
      $assertcontrol(ON, ALL_TYPES, ASSERT|COVER);
      `RUN_ALL_ASSERTS;
      $assertcontrol(ON, ALL_TYPES, ASSUME);
      `RUN_ALL_ASSERTS;
      $assertoff;
      `RUN_ALL_ASSERTS;
      $assertcontrol(ON, SIMPLE_IMMEDIATE|FINAL_DEFERRED_IMMEDIATE, COVER|ASSUME);
      `RUN_ALL_ASSERTS;
      $assertoff;

      // concurrent test
      #10;
      $display("Disabling concurrent asserts, time: %g", $time);
      $assertcontrol(ON, ALL_TYPES);
      $assertcontrol(OFF, CONCURRENT);
      #10;
      $display("Enabling concurrent asserts, time: %g", $time);
      $assertcontrol(ON, CONCURRENT);
      $finish;
   end
endmodule

task run_all_asserts(string file, integer line);
   run_simple_immediate(file, line);
   run_observed_deferred_immediate(file, line);
   run_final_deferred_immediate(file, line);
endtask

task run_simple_immediate(string file, integer line);
   $display("Testing assert_simple_immediate at %s:%g", file, line);
   assert_simple_immediate: assert(0);
   assert_simple_immediate_else: assert(0) else `DISPLAY_FAIL(file, line);
   assert_simple_immediate_stmt: assert(0) `DISPLAY_PASS(file, line);
   assert_simple_immediate_stmt_else: assert(0) `DISPLAY_PASS(file, line); else `DISPLAY_FAIL(file, line);

   $display("Testing assume_simple_immediate at %s:%g", file, line);
   assume_simple_immediate: assume(0);
   assume_simple_immediate_else: assume(0) else `DISPLAY_FAIL(file, line);
   assume_simple_immediate_stmt: assume(0) `DISPLAY_PASS(file, line);
   assume_simple_immediate_stmt_else: assume(0) `DISPLAY_PASS(file, line); else `DISPLAY_FAIL(file, line);
endtask

task run_observed_deferred_immediate(string file, integer line);
   $display("Testing assert_observed_deferred_immediate at %s:%g", file, line);
   assert_observed_deferred_immediate: assert #0 (0);
   assert_observed_deferred_immediate_else: assert #0 (0) else `DISPLAY_FAIL(file, line);
   assert_observed_deferred_immediate_stmt: assert #0 (0) `DISPLAY_PASS(file, line);
   assert_observed_deferred_immediate_stmt_else: assert #0 (0) `DISPLAY_PASS(file, line); else `DISPLAY_FAIL(file, line);

   $display("Testing assume_observed_deferred_immediate at %s:%g", file, line);
   assume_observed_deferred_immediate: assume #0 (0);
   assume_observed_deferred_immediate_else: assume #0 (0) else `DISPLAY_FAIL(file, line);
   assume_observed_deferred_immediate_stmt: assume #0 (0) `DISPLAY_PASS(file, line);
   assume_observed_deferred_immediate_stmt_else: assume #0 (0) `DISPLAY_PASS(file, line); else `DISPLAY_FAIL(file, line);
endtask

task run_final_deferred_immediate(string file, integer line);
   $display("Testing assert_final_deferred_immediate at %s:%g", file, line);
   assert_final_deferred_immediate: assert final (0);
   assert_final_deferred_immediate_else: assert final (0) else `DISPLAY_FAIL(file, line);
   assert_final_deferred_immediate_stmt: assert final (0) `DISPLAY_PASS(file, line);
   assert_final_deferred_immediate_stmt_else: assert final (0) `DISPLAY_PASS(file, line); else `DISPLAY_FAIL(file, line);

   $display("Testing assume_final_deferred_immediate at %s:%g", file, line);
   assume_final_deferred_immediate: assume final (0);
   assume_final_deferred_immediate_else: assume final (0) else `DISPLAY_FAIL(file, line);
   assume_final_deferred_immediate_stmt: assume final (0) `DISPLAY_PASS(file, line);
   assume_final_deferred_immediate_stmt_else: assume final (0) `DISPLAY_PASS(file, line); else `DISPLAY_FAIL(file, line);
endtask

module concurrent(input clk);
   property prop();
      @(posedge clk) 0
   endproperty

   assert_concurrent: assert property (prop);
   assert_concurrent_else: assert property(prop) else `DISPLAY_FAIL(`__FILE__, `__LINE__);
   assert_concurrent_stmt: assert property(prop) `DISPLAY_PASS(`__FILE__, `__LINE__);
   assert_concurrent_stmt_else: assert property(prop) `DISPLAY_PASS(`__FILE__, `__LINE__); else `DISPLAY_FAIL(`__FILE__, `__LINE__);

   assume_concurrent: assume property(prop);
   assume_concurrent_else: assume property(prop) else `DISPLAY_FAIL(`__FILE__, `__LINE__);
   assume_concurrent_stmt: assume property(prop) `DISPLAY_PASS(`__FILE__, `__LINE__);
   assume_concurrent_stmt_else: assume property(prop) `DISPLAY_PASS(`__FILE__, `__LINE__); else `DISPLAY_FAIL(`__FILE__, `__LINE__);

   cover_concurrent: cover property(prop);
   cover_concurrent_stmt: cover property(prop) `DISPLAY_PASS(`__FILE__, `__LINE__);
endmodule
