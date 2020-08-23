// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2020 by Peter Monsson.

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

   reg [31:0]   dly0 = -1;

   // If called in an assertion, sequence, or property, the appropriate clocking event.
   // Otherwise, if called in a disable condition or a clock expression in an assertion, sequence, or prop, explicit.
   // Otherwise, if called in an action block of an assertion, the leading clock of the assertion is used.
   // Otherwise, if called in a procedure, the inferred clock
   // Otherwise, default clocking

   always @(posedge clk) begin
      dly0 <= in;
      // In clock expression
      $write("dly0=%0d, in=%0d, stable=%0d, past=%0d\n", dly0, in, $stable(dly0), $past(dly0));
      if ($stable(dly0)) $stop;
      if (!$changed(dly0)) $stop;
   end

   assert property (@(posedge clk) !$stable(dly0));
   assert property (@(posedge clk) $changed(dly0));
endmodule

module Test2 (/*AUTOARG*/
   // Inputs
   clk, in
   );

   input clk;
   input [31:0] in;

   reg [31:0]   dly0;

   always @(posedge clk) begin
      dly0 <= in;
      if (!$stable(dly0[31:4])) $stop;
      if ($changed(dly0[31:4])) $stop;
   end

   default clocking @(posedge clk); endclocking
   assert property ($stable(dly0[31:4]));
   assert property (!$changed(dly0[31:4]));
endmodule
