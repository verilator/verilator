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

   clock_init_race clock_init_race(.clk(clk), .reset_l(reset_l));

   parametrized_always#(.PARAM(0)) parametrized_always0(.clk(clk));
   parametrized_always#(.PARAM(1)) parametrized_always1(.clk(clk));
   parametrized_always#(.PARAM(2)) parametrized_always2(.clk(clk));

   parametrized_initial#(.PARAM(0)) parametrized_initial0();
   parametrized_initial#(.PARAM(1)) parametrized_initial1();
   parametrized_initial#(.PARAM(2)) parametrized_initial2();

   const_condition const_condition();
   loop_with_param loop_with_param();
   if_with_param if_with_param();
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

// module unused - no warning for any of statements inside
module unused(input clk);
   reg unused_variable_while = 0;
   reg unused_variable_do_while = 0;
   reg unused_variable_for = 0;
   logic always_false = 0;

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
         $write("This will not be printed");
      end

      do begin
         $write("This will not be printed");
      end while (always_false);

      for (int i = 0; always_false; i++)
      begin
         $write("This will not be printed");
      end
   end
endmodule

module parametrized_always #(parameter PARAM = 1)(input clk);
   int prints_while = 0;
   int prints_do_while = 0;

   // loops with evaluation depending on PARAM - no warning
   always @(posedge clk) begin
      while(prints_while < PARAM) begin
         prints_while <= prints_while + 1;
         $write("Writing to console to avoid loop being optimized out\n");
      end

      while(PARAM < 0) begin
         $write("Writing to console to avoid loop being optimized out\n");
      end

      for (int i = 0; i < PARAM; i++) begin
         $write("Writing to console to avoid loop being optimized out\n");
      end

      do begin
         prints_do_while <= prints_do_while + 1;
         $write("Writing to console to avoid loop being optimized out\n");
      end while (prints_do_while < PARAM);

      // infinite loop warning
      while(PARAM == 1) begin
         $write("Writing to console to avoid loop being optimized out\n");
      end

      // infinite loop warning
      for (int i = 0; PARAM == 0; i++) begin
         $write("Writing to console to avoid loop being optimized out\n");
      end
   end

   // loop not changing variable used for output
   int param_unused_while = 0;
   int param_unused_do_while = 0;
   int param_unused_for = 0;
   always @(posedge clk) begin
      // unused loop warning
      while(param_unused_while < PARAM) begin
            param_unused_while <= param_unused_while + 1;
      end

      // inlined - no warning
      do begin
            param_unused_do_while <= 1;
      end while (param_unused_do_while > 0);

      // unrolled - no warning
      for (int i = 0; i < 5; i++)
      begin
         param_unused_for <= 1;
      end
   end

   // loop with stdout - no warning
   always @(posedge clk) begin
      for (int i = 0; i < 1; i++)
      begin
         $write("Writing to console to avoid loop being optimized out\n");
      end
   end

   // loops with empty bodies
   logic param_always_false = 0;
   logic param_always_true = !param_always_false;
   always @(posedge clk) begin
      while(1); // both infinite loop and unused loop warnings
      while(param_always_true); // both infinite loop and unused loop warnings
      while(PARAM == 1); // both infinite loop and unused loop warnings

      while(0); // TODO should be warning
      while(param_always_false);
      while(PARAM < 0); // TODO should be warning

      // unrolled - no warning
      for (int i = 0; i < 1; i++);

      // inlined - no warning
      do begin
      end
      while(0);

      // infinite loop warning, no unused loop warning
      do begin
      end
      while(1);
   end
endmodule

module parametrized_initial #(parameter PARAM = 0);
 int prints_while = 0;
   int prints_do_while = 0;

   // loops with evaluation depending on PARAM - no warning
   initial begin
      while(prints_while < PARAM) begin
         prints_while = prints_while + 1;
         $write("Writing to console to avoid loop being optimized out\n");
      end

      while(PARAM < 0) begin
         $write("Writing to console to avoid loop being optimized out\n");
      end

      for (int i = 0; i < PARAM; i++) begin
         $write("Writing to console to avoid loop being optimized out\n");
      end

      do begin
         prints_do_while = prints_do_while + 1;
         $write("Writing to console to avoid loop being optimized out\n");
      end while (prints_do_while < PARAM);

      // infinite loop warning, no unused loop warning
      for (int i = 0; PARAM == 0; i++) begin
         $write("Writing to console to avoid loop being optimized out\n");
      end

      // infinite loop warning, no unused loop warning
      while(PARAM == 1) begin
         $write("Writing to console to avoid loop being optimized out\n");
      end
   end

   // loop not changing variable used for output
   int param_unused_while = 0;
   int param_unused_do_while = 0;
   int param_unused_for = 0;
   initial begin
      // unused loop warning
      while(param_unused_while < PARAM) begin
            param_unused_while = param_unused_while + 1;
      end

      // inlined - no warning
      do begin
            param_unused_do_while = 1;
      end while (param_unused_do_while > 0);

      // unrolled - no warning
      for (int i = 0; i < 5; i++)
      begin
         param_unused_for = 1;
      end
   end

   // loop with stdout - no warning
   initial begin
      for (int i = 0; i < 1; i++)
      begin
         $write("Writing to console to avoid loop being optimized out\n");
      end
   end

   logic param_always_false = 0;
   logic param_always_true = !param_always_false;
   // loops with empty bodies
   initial begin
      while(1); // both infinite and unused loop warnings
      while(param_always_true); // infinite loop, TODO check if unused loop needed
      while(PARAM == 1); // infinite loop, TODO check if unused loop needed

      while(0); // TODO should be warning
      while(param_always_false); // TODO should be warning
      while(PARAM < 0); // TODO should be warning

      // unrolled, no warning
      for (int i = 0; i < 1; i++);
   end
endmodule

module const_condition();
   logic param_always_false = 0;
   // loops with const false condition - warning
   initial begin
      while(param_always_false) begin
         $write("This will not be printed");
      end

      for (int i = 0; param_always_false; i++)
      begin
         $write("This will not be printed");
      end

      for (int i = 0; i < param_always_false; i++)
      begin
         $write("This will not be printed");
      end

      // inlined - no warning
      do begin
         $write("This will be printed");
      end while (param_always_false);
   end
endmodule

module loop_with_param();
   parameter ZERO_PARAM = 0;
   parameter ONE_PARAM = 1;

   initial begin
      // loop condition false - warning unused loop
      for (int i = 0; ZERO_PARAM; i++) begin
         $write("This will not be printed");
      end

      // loop condition true - warning infinite loop
      for (int i = 0; ONE_PARAM; i++) begin
         $write("Writing to infinitely");
      end
   end
endmodule

module if_with_param();
   parameter ZERO_PARAM = 0;
   parameter ONE_PARAM = 1;

   initial begin
      if (ZERO_PARAM) begin
         // loop under false parametrized if - no warning
         for (int i = 0; i < 5; i++) begin
            $write("Writing to console");
         end

         // loop under if but unused anyway - warning
         while(0);
      end else if (!ONE_PARAM) begin
         // loop under false parametrized if - no warning
         for (int i = 0; i < 2; i++) begin
            $write("Writing to console");
         end

         // loop under if but unused anyway - warning
         while(0);
      end else begin
         // loop under true parametrized if - no warning
         for (int i = 0; i < 1; i++) begin
            $write("Writing to console");
         end

         // loop under if but unused anyway - warning
         while(0);
      end

      // loop unused - warning
      while(0);
   end
endmodule
