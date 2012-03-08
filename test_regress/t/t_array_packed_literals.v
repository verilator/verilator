// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2009 by Iztok Jeras.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   // parameters for array sizes
   localparam WA = 4;  // address dimension size
   localparam WB = 4;  // bit     dimension size

   localparam NO = 10;  // number of access events

   // 2D packed arrays
   logic [WA-1:0] [WB-1:0] array_bg;  // big endian array
   /* verilator lint_off LITENDIAN */
   logic [0:WA-1] [0:WB-1] array_lt;  // little endian array
   /* verilator lint_on LITENDIAN */

   integer cnt = 0;

   // event counter
   always @ (posedge clk) begin
      cnt <= cnt + 1;
   end

   // finish report
   always @ (posedge clk)
     if ((cnt[30:2]==(NO-1)) && (cnt[1:0]==2'd3)) begin
	$write("*-* All Finished *-*\n");
	$finish;
     end

   // big endian
   always @ (posedge clk)
     if (cnt[1:0]==2'd0) begin
	// initialize to defaults (all bits 1'bx)
	if      (cnt[30:2]==0)  array_bg <=  {WA{ {WB{1'bx}} }};
	else if (cnt[30:2]==1)  array_bg <=  {WA{ {WB{1'bx}} }};
	else if (cnt[30:2]==2)  array_bg <=  {WA{ {WB{1'bx}} }};
	else if (cnt[30:2]==3)  array_bg <=  {WA{ {WB{1'bx}} }};
	else if (cnt[30:2]==4)  array_bg <=  {WA{ {WB{1'bx}} }};
	else if (cnt[30:2]==5)  array_bg <=  {WA{ {WB{1'bx}} }};
	else if (cnt[30:2]==6)  array_bg <=  {WA{ {WB{1'bx}} }};
	else if (cnt[30:2]==7)  array_bg <=  {WA{ {WB{1'bx}} }};
	else if (cnt[30:2]==8)  array_bg <=  {WA{ {WB{1'bx}} }};
	else if (cnt[30:2]==9)  array_bg <=  {WA{ {WB{1'bx}} }};
     end else if (cnt[1:0]==2'd1) begin
	// write data into whole or part of the array using literals
	if      (cnt[30:2]==0)  begin end
	else if (cnt[30:2]==1)  array_bg               = '{ 3 ,2 ,1, 0 };
	else if (cnt[30:2]==2)  array_bg               = '{0:4, 1:5, 2:6, 3:7};
	else if (cnt[30:2]==3)  array_bg               = '{default:13};
	else if (cnt[30:2]==4)  array_bg               = '{2:15, default:13};
	else if (cnt[30:2]==5)  array_bg               = '{WA  {          {WB/2  {2'b10}}  }};
	else if (cnt[30:2]==6)  array_bg               = '{WA  { {3'b101, {WB/2-1{2'b10}}} }};
	else if (cnt[30:2]==7)  array_bg               = '{WA  {          {WB/2-1{2'b10}}  }};
	else if (cnt[30:2]==8)  array_bg [WA/2-1:0   ] = '{WA/2{          {WB/2  {2'b10}}  }};
	else if (cnt[30:2]==9)  array_bg [WA  -1:WA/2] = '{WA/2{          {WB/2  {2'b01}}  }};
     end else if (cnt[1:0]==2'd2) begin
	// chack array agains expected value
	if      (cnt[30:2]==0)  begin if (array_bg !== 16'bxxxxxxxxxxxxxxxx) begin $display("%b", array_bg); $stop(); end end
	else if (cnt[30:2]==1)  begin if (array_bg !== 16'b0011001000010000) begin $display("%b", array_bg); $stop(); end end
	else if (cnt[30:2]==2)  begin if (array_bg !== 16'b0111011001010100) begin $display("%b", array_bg); $stop(); end end
	else if (cnt[30:2]==3)  begin if (array_bg !== 16'b1101110111011101) begin $display("%b", array_bg); $stop(); end end
	else if (cnt[30:2]==4)  begin if (array_bg !== 16'b1101111111011101) begin $display("%b", array_bg); $stop(); end end
	else if (cnt[30:2]==5)  begin if (array_bg !== 16'b1010101010101010) begin $display("%b", array_bg); $stop(); end end
	else if (cnt[30:2]==6)  begin if (array_bg !== 16'b0110011001100110) begin $display("%b", array_bg); $stop(); end end
	else if (cnt[30:2]==7)  begin if (array_bg !== 16'b0010001000100010) begin $display("%b", array_bg); $stop(); end end
	else if (cnt[30:2]==8)  begin if (array_bg !== 16'b10101010xxxxxxxx) begin $display("%b", array_bg); $stop(); end end
	else if (cnt[30:2]==9)  begin if (array_bg !== 16'bxxxxxxxx10101010) begin $display("%b", array_bg); $stop(); end end
     end

   // little endian
   always @ (posedge clk)
     if (cnt[1:0]==2'd0) begin
	// initialize to defaults (all bits 1'bx)
	if      (cnt[30:2]==0)  array_lt <=  {WA{ {WB{1'bx}} }};
	else if (cnt[30:2]==1)  array_lt <=  {WA{ {WB{1'bx}} }};
	else if (cnt[30:2]==2)  array_lt <=  {WA{ {WB{1'bx}} }};
	else if (cnt[30:2]==3)  array_lt <=  {WA{ {WB{1'bx}} }};
	else if (cnt[30:2]==4)  array_lt <=  {WA{ {WB{1'bx}} }};
	else if (cnt[30:2]==5)  array_lt <=  {WA{ {WB{1'bx}} }};
	else if (cnt[30:2]==6)  array_lt <=  {WA{ {WB{1'bx}} }};
	else if (cnt[30:2]==7)  array_lt <=  {WA{ {WB{1'bx}} }};
	else if (cnt[30:2]==8)  array_lt <=  {WA{ {WB{1'bx}} }};
	else if (cnt[30:2]==9)  array_lt <=  {WA{ {WB{1'bx}} }};
     end else if (cnt[1:0]==2'd1) begin
	// write data into whole or part of the array using literals
	if      (cnt[30:2]==0)  begin end
	else if (cnt[30:2]==1)  array_lt               = '{ 3 ,2 ,1, 0 };
	else if (cnt[30:2]==2)  array_lt               = '{3:4, 2:5, 1:6, 0:7};
	else if (cnt[30:2]==3)  array_lt               = '{default:13};
	else if (cnt[30:2]==4)  array_lt               = '{1:15, default:13};
	else if (cnt[30:2]==5)  array_lt               = '{WA  {          {WB/2  {2'b10}}  }};
	else if (cnt[30:2]==6)  array_lt               = '{WA  { {3'b101, {WB/2-1{2'b10}}} }};
	else if (cnt[30:2]==7)  array_lt               = '{WA  {          {WB/2-1{2'b10}}  }};
	else if (cnt[30:2]==8)  array_lt [0   :WA/2-1] = '{WA/2{          {WB/2  {2'b10}}  }};
	else if (cnt[30:2]==9)  array_lt [WA/2:WA  -1] = '{WA/2{          {WB/2  {2'b01}}  }};
     end else if (cnt[1:0]==2'd2) begin
	// chack array agains expected value
	if      (cnt[30:2]==0)  begin if (array_lt !== 16'bxxxxxxxxxxxxxxxx) begin $display("%b", array_lt); $stop(); end end
	else if (cnt[30:2]==1)  begin if (array_lt !== 16'b0011001000010000) begin $display("%b", array_lt); $stop(); end end
	else if (cnt[30:2]==2)  begin if (array_lt !== 16'b0111011001010100) begin $display("%b", array_lt); $stop(); end end
	else if (cnt[30:2]==3)  begin if (array_lt !== 16'b1101110111011101) begin $display("%b", array_lt); $stop(); end end
	else if (cnt[30:2]==4)  begin if (array_lt !== 16'b1101111111011101) begin $display("%b", array_lt); $stop(); end end
	else if (cnt[30:2]==5)  begin if (array_lt !== 16'b1010101010101010) begin $display("%b", array_lt); $stop(); end end
	else if (cnt[30:2]==6)  begin if (array_lt !== 16'b0110011001100110) begin $display("%b", array_lt); $stop(); end end
	else if (cnt[30:2]==7)  begin if (array_lt !== 16'b0010001000100010) begin $display("%b", array_lt); $stop(); end end
	else if (cnt[30:2]==8)  begin if (array_lt !== 16'b10101010xxxxxxxx) begin $display("%b", array_lt); $stop(); end end
	else if (cnt[30:2]==9)  begin if (array_lt !== 16'bxxxxxxxx10101010) begin $display("%b", array_lt); $stop(); end end
     end

endmodule
