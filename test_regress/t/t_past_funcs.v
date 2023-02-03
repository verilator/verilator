// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2020 by Peter Monsson.
// SPDX-License-Identifier: Unlicense

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   integer cyc; initial cyc=1;
   wire [31:0] in = cyc;

   Test test (/*AUTOINST*/
              // Inputs
              .clk                      (clk),
              .in                       (in[31:0]));

   Test2 test2 (/*AUTOINST*/
                // Inputs
                .clk                    (clk),
                .in                     (in[31:0]));

   Test3 test3 (/*AUTOINST*/
                // Inputs
                .clk                    (clk),
                .in                     (in[31:0]));

   always @ (posedge clk) begin
      if (cyc!=0) begin
         cyc <= cyc + 1;
         if (cyc==10) begin
            $write("*-* All Finished *-*\n");
            $finish;
         end
      end
   end

endmodule

module Test (/*AUTOARG*/
   // Inputs
   clk, in
   );

   input clk;
   input [31:0] in;

   reg [31:0]   dly0 = 0;
   reg [31:0]   dly1 = 1;
   reg [31:0]   dly2 = -1;

   // If called in an assertion, sequence, or property, the appropriate clocking event.
   // Otherwise, if called in a disable condition or a clock expression in an assertion, sequence, or prop, explicit.
   // Otherwise, if called in an action block of an assertion, the leading clock of the assertion is used.
   // Otherwise, if called in a procedure, the inferred clock
   // Otherwise, default clocking

   always @(posedge clk) begin
      dly0 <= in;
      dly1 <= in;
      dly2 <= in;
      // In clock expression
      $write("in=%0d, dly0=%0d, rose=%0d, past=%0d\n", in, dly0, $rose(dly0), $past(dly0));
      if ($rose(dly0[4])) $stop;
      if ($fell(dly1[4])) $stop;
      if ($stable(dly2)) $stop;
      if (!$changed(dly2)) $stop;
   end

   assert property (@(posedge clk) $rose(dly0) || dly0%2==0);
   assert property (@(posedge clk) $fell(dly1) || dly1%2==1);
   assert property (@(posedge clk) !$stable(dly2));
   assert property (@(posedge clk) $changed(dly2));

   global clocking @(posedge clk); endclocking
   always @ ($global_clock) $display("%d", in);
   //
   assert property (@(posedge clk) $rose(dly0, $global_clock) || dly0%2==0);
   assert property (@(posedge clk) $fell(dly1, $global_clock) || dly1%2==1);
   assert property (@(posedge clk) !$stable(dly2, $global_clock));
   assert property (@(posedge clk) $changed(dly2, $global_clock));
   //
   assert property (@(posedge clk) $rose_gclk(dly0) || dly0%2==0);
   assert property (@(posedge clk) $fell_gclk(dly1) || dly1%2==1);
   assert property (@(posedge clk) !$stable_gclk(dly2));
   assert property (@(posedge clk) $changed_gclk(dly2));

   // global_clocking_future_functions are not supported yet:
   // $changing_gclk     global_clocking_future_function
   // $falling_gclk      global_clocking_future_function
   // $future_gclk       global_clocking_future_function
   // $rising_gclk       global_clocking_future_function
   // $steady_gclk       global_clocking_future_function

endmodule


module Test2 (/*AUTOARG*/
   // Inputs
   clk, in
   );

   input clk;
   input [31:0] in;

   reg [31:0]   dly0;
   reg [31:0]   dly1 = 1;
   reg [31:0]   dly2;

   always @(posedge clk) begin
      dly0 <= in;
      dly1 <= in;
      dly2 <= in;
      if ($rose(dly0[31:4])) $stop;
      if ($fell(dly1[31:4])) $stop;
      if (!$stable(dly2[31:4])) $stop;
      if ($changed(dly2[31:4])) $stop;
   end

   default clocking @(posedge clk); endclocking

   assert property ($rose(dly0[0]) || dly0%2==0);
   assert property ($fell(dly1[0]) || dly1%2==1);
   assert property ($stable(dly2[31:4]));
   assert property (!$changed(dly2[31:4]));
endmodule

module Test3 (/*AUTOARG*/
   // Inputs
   clk, in
   );

   input clk;
   input [31:0] in;

   // Check the named form of global clocking
   global clocking gck @(posedge clk); endclocking
   always @ (gck) $display("%d", in);
   always @ ($global_clock) $display("%d", in);

endmodule
