// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

// verilator lint_off BLKSEQ
// verilator lint_off DECLFILENAME

module t(/*AUTOARG*/
   // Inputs
   clk, reset_l
   );
   input clk;
   input reset_l;

   parametrized_initial#(.REPETITIONS(0)) parametrized_initial0();
   parametrized_initial#(.REPETITIONS(1)) parametrized_initial1();
   parametrized_initial#(.REPETITIONS(2)) parametrized_initial2();
   non_parametrized_initial non_parametrized_initial();

   with_always with_always(.clk(clk));
   const_condition const_condition();
   loop_with_param loop_with_param();
   if_with_param if_with_param();
   clock_init_race clock_init_race(.clk(clk), .reset_l(reset_l));
endmodule

// module unused - no warning for any of statements inside
module unused(input clk);
   reg unused_variable_while = 0;
   reg unused_variable_do_while = 0;
   reg unused_variable_for = 0;
   const logic always_false = 0;

   always @(posedge clk) begin
      while(unused_variable_while) begin
            unused_variable_while <= 1;
      end

      do begin
            unused_variable_do_while <= 1;
      end while (unused_variable_do_while);

      for (int i = 0; i < 5; i++)
      begin
         unused_variable_for <= 1;
      end

      while(always_false) begin
         $write("This will not be printed\n");
      end

      do begin
         $write("This will not be printed\n");
      end while (always_false);

      for (int i = 0; always_false; i++)
      begin
         $write("This will not be printed\n");
      end
   end
endmodule

// no warning for loops under parametrized module
module parametrized_initial #(parameter REPETITIONS = 0);
   int prints_while = 0;
   int prints_do_while = 0;

   // loops with evaluation depending on REPETITIONS
   initial begin
      while(prints_while < REPETITIONS) begin
         prints_while = prints_while + 1;
         $write("Writing to console to avoid loop being optimized out\n");
      end

      while(REPETITIONS < 0) begin
         $write("Writing to console to avoid loop being optimized out\n");
      end

      for (int i = 0; i < REPETITIONS; i++) begin
         $write("Writing to console to avoid loop being optimized out\n");
      end

      do begin
         prints_do_while = prints_do_while + 1;
         $write("Writing to console to avoid loop being optimized out\n");
      end while (prints_do_while < REPETITIONS);
   end

   // loop not changing variable used for output
   int param_unused_while = 0;
   initial begin
      while(param_unused_while < REPETITIONS) begin
            param_unused_while = param_unused_while + 1;
      end
   end

   const logic always_false = 0;
   // loops with empty bodies
   initial begin
      while(0);
      while(always_false);
      while(REPETITIONS < 0);
   end
endmodule

module non_parametrized_initial;
   int prints_do_while = 0;
   const int always_zero = 0;

   // loops with evaluation depending on always_zero
   initial begin
      while(always_zero < 0) begin
         $write("This will not be printed\n");
      end

      // unrolled - no warning
      for (int i = 0; i < always_zero; i++) begin
         $write("This will not be printed\n");
      end

      // inlined - no warning
      do begin
         prints_do_while = prints_do_while + 1;
         $write("Writing to console to avoid loop being optimized out\n");
      end while (prints_do_while < always_zero);
   end

   // loop not changing variable used for output
   int param_unused_while = 0;
   int param_unused_do_while = 0;
   int param_unused_for = 0;
   initial begin
      // warning
      while(param_unused_while < always_zero) begin
            param_unused_while++;
      end

      // unrolled - no warning
      for (int i = 0; i < 5; i++)
      begin
         param_unused_for = 1;
      end

      // inlined - no warning
      do begin
            param_unused_do_while = 1;
      end while (param_unused_do_while > 0);
   end

   const logic always_false = 0;
   // loops with empty bodies - warning
   initial begin
      while(0);
      while(always_false);
      while(always_zero < 0);

      // inlined - no warning
      do begin
      end while(0);

      // unrolled - no warning
      for (int i = 0; i < 1; i++);
   end
endmodule

// warning for all unused loops under always
module with_always(input clk);
   const logic always_false = 0;
   always @(posedge clk) begin
      while(0);

      while(always_false) begin
         $write("Test");
      end
   end
endmodule

module const_condition;
   const logic always_zero = 0;
   // loops with const false condition - warning
   initial begin
      while(always_zero) begin
         $write("This will not be printed\n");
      end

      for (int i = 0; always_zero; i++)
      begin
         $write("This will not be printed\n");
      end

      for (int i = 0; i < always_zero; i++)
      begin
         $write("This will not be printed\n");
      end

      // inlined - no warning
      do begin
         $write("This will be printed\n");
      end while (always_zero);
   end
endmodule

// loop with param - no warning
module loop_with_param;
   parameter ZERO_PARAM = 0;
   int prints = 2;

   initial begin
      for (int i = 0; ZERO_PARAM; i++) begin
         $write("This will not be printed\n");
      end

      while (ZERO_PARAM != ZERO_PARAM) begin
         $write("This will not be printed\n");
      end

      while(prints > ZERO_PARAM) begin
         prints--;
      end
   end
endmodule

module if_with_param;
   parameter ZERO_PARAM = 0;
   parameter ONE_PARAM = 1;

   initial begin
      if (ZERO_PARAM) begin
         // loop under false parametrized if - no warning
         int prints = 0;
         while(prints < 5) begin
            prints++;
         end
         $write("Prints %d\n", prints);
      end else if (!ONE_PARAM) begin
         // loop under false parametrized if - no warning
         int prints = 0;
         while(prints < 5) begin
            prints++;
         end
         $write("Prints %d\n", prints);
      end else begin
         // loop under true parametrized if - no warning
         int prints = 0;
         while(prints < 5) begin
            prints++;
         end
         $write("Prints %d\n", prints);
      end
   end
endmodule

module clock_init_race(input clk, input reset_l);
   logic m_2_clock;
   logic m_3_clock;
   logic m_2_reset = reset_l;
   logic m_3_reset = reset_l;
   assign m_2_clock = clk;
   assign m_3_clock = clk;
   int m_3_counter = 0;
   initial begin
      $write("*-* START TEST *-*\n");
   end

   always @(posedge clk) begin
      if (m_3_counter == 25) begin
         $write("*-* All Finished *-*\n");
         $finish();
      end
   end

   reg m_2_ticked = 1'b0;
   always @(posedge m_2_clock) if (!m_2_reset) begin
      m_2_ticked = 1'b1;
   end
   always @(negedge m_2_clock) m_2_ticked = 1'b0;

   always @(posedge m_3_clock) if (!m_3_reset) begin
      $write("*-* m_3_clocked *-*\n");
      // loop empty - unused loop warning
      while (m_2_ticked);
      m_3_counter += 1;
   end
endmodule
