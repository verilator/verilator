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

   reg [31:0]   dly0 = 0;

   // If called in an assertion, sequence, or property, the appropriate clocking event.
   // Otherwise, if called in a disable condition or a clock expression in an assertion, sequence, or prop, explicit.
   // Otherwise, if called in an action block of an assertion, the leading clock of the assertion is used.
   // Otherwise, if called in a procedure, the inferred clock
   // Otherwise, default clocking

   always @(posedge clk) begin
      dly0 <= in;
      // In clock expression
      $write("in=%0d, dly0=%0d, rose=%0d, past=%0d\n", in, dly0, $rose(dly0), $past(dly0));
      if ($rose(dly0[4])) $stop;
   end

   assert property (@(posedge clk) $rose(dly0) || dly0%2==0);
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
      if ($rose(dly0[31:4])) $stop;
   end

   default clocking @(posedge clk); endclocking
   assert property ($rose(dly0[0]) || dly0%2==0);
endmodule
