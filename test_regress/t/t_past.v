// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2018 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer      cyc=0;
   reg [63:0]   crc;
   reg [63:0]   sum;

   // Take CRC data and apply to testblock inputs
   wire [31:0]  in = crc[31:0];

   Test test (/*AUTOINST*/
              // Inputs
              .clk                      (clk),
              .in                       (in[31:0]));

   Test2 test2 (/*AUTOINST*/
                // Inputs
                .clk                    (clk),
                .in                     (in[31:0]));

   // Test loop
   always @ (posedge clk) begin
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63]^crc[2]^crc[0]};
      if (cyc==0) begin
         // Setup
         crc <= 64'h5aef0c8d_d70a4497;
      end
      else if (cyc<10) begin
      end
      else if (cyc<90) begin
      end
      else if (cyc==99) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule

module Test (/*AUTOARG*/
   // Inputs
   clk, in
   );

   input clk;
   input [31:0] in;

   reg [31:0]   dly0;
   reg [31:0]   dly1;
   reg [31:0]   dly2;
   reg [31:0]   dly3;

   // If called in an assertion, sequence, or property, the appropriate clocking event.
   // Otherwise, if called in a disable condition or a clock expression in an assertion, sequence, or prop, explicit.
   // Otherwise, if called in an action block of an assertion, the leading clock of the assertion is used.
   // Otherwise, if called in a procedure, the inferred clock
   // Otherwise, default clocking

   always @(posedge clk) begin
      dly0 <= in;
      dly1 <= dly0;
      dly2 <= dly1;
      dly3 <= dly2;
      // $past(expression, ticks, expression, clocking)
      // In clock expression
      if (dly0 != $past(in)) $stop;
      if (dly0 != $past(in,1)) $stop;
      if (dly1 != $past(in,2)) $stop;
      // $sampled(expression) -> expression
      if (in != $sampled(in)) $stop;
   end

   assert property (@(posedge clk) dly0 == $past(in));

endmodule

module Test2 (/*AUTOARG*/
   // Inputs
   clk, in
   );

   input clk;
   input [31:0] in;

   reg [31:0]   dly0;
   reg [31:0]   dly1;

   always @(posedge clk) begin
      dly0 <= in;
      dly1 <= dly0;
   end

   default clocking @(posedge clk); endclocking
   assert property (@(posedge clk) $time < 40 || dly1 == $past(in, 2));

endmodule
