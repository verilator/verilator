// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2005 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   fastclk, clk
   );

`ifdef EDGE_DETECT_STYLE        // Two 'common' forms of latching, with full combo, and with pos/negedge
 `define posstyle posedge
 `define negstyle negedge
`else
 `define posstyle
 `define negstyle
`endif

   input fastclk;
   input clk;

   reg [7:0] data;
   reg [7:0] data_a;
   reg [7:0] data_a_a;
   reg [7:0] data_a_b;
   reg [7:0] data_b;
   reg [7:0] data_b_a;
   reg [7:0] data_b_b;

   reg [8*6-1:0] check [100:0];
   wire [8*6-1:0] compare = {data_a,data_a_a,data_b_a,data_b,data_a_b,data_b_b};
   initial begin
      check[7'd19] = {8'h0d, 8'h0e, 8'h0e, 8'h0d, 8'h0e, 8'h0e};
      check[7'd20] = {8'h0d, 8'h0e, 8'h0e, 8'h0d, 8'h0e, 8'h0e};
      check[7'd21] = {8'h15, 8'h16, 8'h0e, 8'h0d, 8'h0e, 8'h0e};
      check[7'd22] = {8'h15, 8'h16, 8'h0e, 8'h0d, 8'h0e, 8'h0e};
      check[7'd23] = {8'h15, 8'h16, 8'h0e, 8'h15, 8'h16, 8'h0e};
      check[7'd24] = {8'h15, 8'h16, 8'h0e, 8'h15, 8'h16, 8'h0e};
      check[7'd25] = {8'h15, 8'h16, 8'h0e, 8'h15, 8'h16, 8'h0e};
      check[7'd26] = {8'h15, 8'h16, 8'h16, 8'h15, 8'h16, 8'h0e};
      check[7'd27] = {8'h15, 8'h16, 8'h16, 8'h15, 8'h16, 8'h0e};
      check[7'd28] = {8'h15, 8'h16, 8'h16, 8'h15, 8'h16, 8'h16};
      check[7'd29] = {8'h15, 8'h16, 8'h16, 8'h15, 8'h16, 8'h16};
      check[7'd30] = {8'h15, 8'h16, 8'h16, 8'h15, 8'h16, 8'h16};
      check[7'd31] = {8'h1f, 8'h20, 8'h16, 8'h15, 8'h16, 8'h16};
      check[7'd32] = {8'h1f, 8'h20, 8'h16, 8'h15, 8'h16, 8'h16};
      check[7'd33] = {8'h1f, 8'h20, 8'h16, 8'h1f, 8'h20, 8'h16};
      check[7'd34] = {8'h1f, 8'h20, 8'h16, 8'h1f, 8'h20, 8'h16};
      check[7'd35] = {8'h1f, 8'h20, 8'h16, 8'h1f, 8'h20, 8'h16};
      check[7'd36] = {8'h1f, 8'h20, 8'h20, 8'h1f, 8'h20, 8'h16};
      check[7'd37] = {8'h1f, 8'h20, 8'h20, 8'h1f, 8'h20, 8'h16};
   end

   // verilator lint_off COMBDLY
   // verilator lint_off LATCH
   always @ (`posstyle clk /*AS*/ or data) begin
      if (clk) begin
         data_a <= data + 8'd1;
      end
   end

   always @ (`posstyle clk /*AS*/ or data_a) begin
      if (clk) begin
         data_a_a <= data_a + 8'd1;
      end
   end

   always @ (`posstyle clk /*AS*/ or data_b) begin
      if (clk) begin
         data_b_a <= data_b + 8'd1;
      end
   end

   always @ (`negstyle clk /*AS*/ or data or data_a) begin
      if (~clk) begin
         data_b <= data + 8'd1;
         data_a_b <= data_a + 8'd1;
         data_b_b <= data_b + 8'd1;
      end
   end

   integer cyc; initial cyc = 0;

   always @ (posedge fastclk) begin
      cyc <= cyc+1;
`ifdef TEST_VERBOSE
      $write("%d  %x %x %x  %x %x %x\n",cyc,data_a,data_a_a,data_b_a,data_b,data_a_b,data_b_b);
`endif
      if (cyc>=19 && cyc<36) begin
         if (compare !== check[cyc]) begin
            $write("[%0t] Mismatch, got=%x, exp=%x\n", $time, compare, check[cyc]);
            $stop;
         end
      end
      if (cyc == 10) begin
         data <= 8'd12;
      end
      if (cyc == 20) begin
         data <= 8'd20;
      end
      if (cyc == 30) begin
         data <= 8'd30;
      end
      if (cyc == 40) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
