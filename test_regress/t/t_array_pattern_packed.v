// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2009 by Iztok Jeras.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   logic [1:0] [3:0] [3:0] array_simp;  // descending range array

   logic [3:0]             array_oned;

   initial begin
      array_oned = '{2:1'b1, 0:1'b1, default:1'b0};
      if (array_oned != 4'b0101) $stop;

      array_simp[0] = '{ 4'd3, 4'd2, 4'd1, 4'd0};
      if (array_simp[0] !== 16'h3210) $stop;

      // verilator lint_off WIDTH
      array_simp[0] = '{ 3 ,2 ,1, 0 };
      // verilator lint_on WIDTH
      if (array_simp[0] !== 16'h3210) $stop;

      // Doesn't seem to work for unpacked arrays in other simulators
      //if (array_simp[0] !== 16'h3210) $stop;
      //array_simp[0] = '{ 1:4'd3, default:13};
      //if (array_simp[0] !== 16'hDD3D) $stop;

      array_simp      = '{ '{ 4'd3, 4'd2, 4'd1, 4'd0 }, '{ 4'd1, 4'd2, 4'd3, 4'd4 }};
      if (array_simp !== 32'h3210_1234) $stop;

      // IEEE says '{} allowed only on assignments, not !=, ==.

      // Doesn't seem to work for unpacked arrays in other simulators
      array_simp = '{2{ '{4'd3, 4'd2, 4'd1, 4'd0 } }};
      if (array_simp !== 32'h3210_3210) $stop;

      array_simp = '{2{ '{4{ 4'd3 }} }};
      if (array_simp !== 32'h3333_3333) $stop;

      // Not legal in other simulators - replication doesn't match
      // However IEEE suggests this is legal.
      //array_simp = '{2{ '{2{ 4'd3, 4'd2 }} }};  // Note it's not '{3,2}

      $write("*-* All Finished *-*\n");
      $finish;
   end

   //====================

   // parameters for array sizes
   localparam WA = 4;  // address dimension size
   localparam WB = 4;  // bit     dimension size

   localparam NO = 11;  // number of access events

   // 2D packed arrays
   logic [WA-1:0] [WB-1:0] array_dsc;  // descending range array
   /* verilator lint_off ASCRANGE */
   logic [0:WA-1] [0:WB-1] array_asc;  // ascending range array
   /* verilator lint_on ASCRANGE */

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

   // descending range
   always @ (posedge clk)
   if (cnt[1:0]==2'd0) begin
      // initialize to defaults (all bits 1'b0)
      if      (cnt[30:2]== 0)  array_dsc <= '0;
      else if (cnt[30:2]== 1)  array_dsc <= '0;
      else if (cnt[30:2]== 2)  array_dsc <= '0;
      else if (cnt[30:2]== 3)  array_dsc <= '0;
      else if (cnt[30:2]== 4)  array_dsc <= '0;
      else if (cnt[30:2]== 5)  array_dsc <= '0;
      else if (cnt[30:2]== 6)  array_dsc <= '0;
      else if (cnt[30:2]== 7)  array_dsc <= '0;
      else if (cnt[30:2]== 8)  array_dsc <= '0;
      else if (cnt[30:2]== 9)  array_dsc <= '0;
      else if (cnt[30:2]==10)  array_dsc <= '0;
   end else if (cnt[1:0]==2'd1) begin
      // write data into whole or part of the array using literals
      if      (cnt[30:2]== 0)  begin end
      else if (cnt[30:2]== 1)  array_dsc               <= '{ 3 ,2 ,1, 0 };
      else if (cnt[30:2]== 2)  array_dsc               <= '{default:13};
      else if (cnt[30:2]== 3)  array_dsc               <= '{0:4, 1:5, 2:6, 3:7};
      else if (cnt[30:2]== 4)  array_dsc               <= '{2:15, default:13};
      else if (cnt[30:2]== 5)  array_dsc               <= '{WA  {          {WB/2  {2'b10}}  }};
      else if (cnt[30:2]== 6)  array_dsc               <= '{cnt[3:0]+0, cnt[3:0]+1, cnt[3:0]+2, cnt[3:0]+3};
   end else if (cnt[1:0]==2'd2) begin
      // chack array agains expected value
      if      (cnt[30:2]== 0)  begin if (array_dsc !== 16'b0000000000000000) begin $display("%b", array_dsc); $stop(); end end
      else if (cnt[30:2]== 1)  begin if (array_dsc !== 16'b0011001000010000) begin $display("%b", array_dsc); $stop(); end end
      else if (cnt[30:2]== 2)  begin if (array_dsc !== 16'b1101110111011101) begin $display("%b", array_dsc); $stop(); end end
      else if (cnt[30:2]== 3)  begin if (array_dsc !== 16'b0111011001010100) begin $display("%b", array_dsc); $stop(); end end
      else if (cnt[30:2]== 4)  begin if (array_dsc !== 16'b1101111111011101) begin $display("%b", array_dsc); $stop(); end end
      else if (cnt[30:2]== 5)  begin if (array_dsc !== 16'b1010101010101010) begin $display("%b", array_dsc); $stop(); end end
      else if (cnt[30:2]== 6)  begin if (array_dsc !== 16'b1001101010111100) begin $display("%b", array_dsc); $stop(); end end
   end

   // ascending range
   always @ (posedge clk)
   if (cnt[1:0]==2'd0) begin
      // initialize to defaults (all bits 1'b0)
      if      (cnt[30:2]== 0)  array_asc <= '0;
      else if (cnt[30:2]== 1)  array_asc <= '0;
      else if (cnt[30:2]== 2)  array_asc <= '0;
      else if (cnt[30:2]== 3)  array_asc <= '0;
      else if (cnt[30:2]== 4)  array_asc <= '0;
      else if (cnt[30:2]== 5)  array_asc <= '0;
      else if (cnt[30:2]== 6)  array_asc <= '0;
      else if (cnt[30:2]== 7)  array_asc <= '0;
      else if (cnt[30:2]== 8)  array_asc <= '0;
      else if (cnt[30:2]== 9)  array_asc <= '0;
      else if (cnt[30:2]==10)  array_asc <= '0;
   end else if (cnt[1:0]==2'd1) begin
      // write data into whole or part of the array using literals
      if      (cnt[30:2]== 0)  begin end
      else if (cnt[30:2]== 1)  array_asc               <= '{ 3 ,2 ,1, 0 };
      else if (cnt[30:2]== 2)  array_asc               <= '{default:13};
      else if (cnt[30:2]== 3)  array_asc               <= '{3:4, 2:5, 1:6, 0:7};
      else if (cnt[30:2]== 4)  array_asc               <= '{1:15, default:13};
      else if (cnt[30:2]== 5)  array_asc               <= '{WA  {          {WB/2  {2'b10}}  }};
      else if (cnt[30:2]==10)  array_asc               <= '{cnt[3:0]+0, cnt[3:0]+1, cnt[3:0]+2, cnt[3:0]+3};
   end else if (cnt[1:0]==2'd2) begin
      // chack array agains expected value
      if      (cnt[30:2]== 0)  begin if (array_asc !== 16'b0000000000000000) begin $display("%b", array_asc); $stop(); end end
      else if (cnt[30:2]== 1)  begin if (array_asc !== 16'b0011001000010000) begin $display("%b", array_asc); $stop(); end end
      else if (cnt[30:2]== 2)  begin if (array_asc !== 16'b1101110111011101) begin $display("%b", array_asc); $stop(); end end
      else if (cnt[30:2]== 3)  begin if (array_asc !== 16'b0111011001010100) begin $display("%b", array_asc); $stop(); end end
      else if (cnt[30:2]== 4)  begin if (array_asc !== 16'b1101111111011101) begin $display("%b", array_asc); $stop(); end end
      else if (cnt[30:2]== 5)  begin if (array_asc !== 16'b1010101010101010) begin $display("%b", array_asc); $stop(); end end
      else if (cnt[30:2]==10)  begin if (array_asc !== 16'b1001101010111100) begin $display("%b", array_asc); $stop(); end end
   end

endmodule
