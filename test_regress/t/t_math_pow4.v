// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2014 by Clifford Wolf.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer      cyc = 0;

   wire [31:0] y;
   reg         a;
   test004 sub (/*AUTOINST*/
                // Outputs
                .y                      (y[31:0]),
                // Inputs
                .a                      (a));

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d a=%x y=%x\n", $time, cyc, a, y);
`endif
      cyc <= cyc + 1;
      if (cyc==0) begin
         a <= 0;
      end
      else if (cyc==1) begin
         a <= 1;
         if (y != 32'h0) $stop;
      end
      else if (cyc==2) begin
         if (y != 32'h010000ff) $stop;
      end
      else if (cyc==99) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule

module test004(a, y);
  input a;
  output [31:0] y;

  wire [7:0] y0;
  wire [7:0] y1;
  wire [7:0] y2;
  wire [7:0] y3;
  assign y = {y0,y1,y2,y3};

  localparam [7:0] V0 = +8'sd1 ** -8'sd2; //'h01
  localparam [7:0] V1 = +8'sd2 ** -8'sd2; //'h00
  localparam [7:0] V2 = -8'sd2 ** -8'sd3; //'h00
  localparam [7:0] V3 = -8'sd1 ** -8'sd3; //'hff
  localparam [7:0] ZERO = 0;

   initial $display("V0=%x V1=%x V2=%x V3=%x", V0,V1,V2,V3);

  assign y0 = a ? V0 : ZERO;
  assign y1 = a ? V1 : ZERO;
  assign y2 = a ? V2 : ZERO;
  assign y3 = a ? V3 : ZERO;
endmodule
