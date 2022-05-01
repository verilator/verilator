// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2014 by Glen Gibb.
// SPDX-License-Identifier: CC0-1.0

//module t;
module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   integer cyc; initial cyc=1;


   // The 'initial' code block below tests compilation-time
   // evaluation/optimization of the stream operator.  All occurences of the stream
   // operator within this block are replaced prior to generation of C code.
   logic [3:0] dout;
   logic [31:0] dout32;
   logic [10:0] dout11;

   initial begin

      // Stream operator: <<
      // Location: rhs of assignment
      //
      // Test slice sizes from 1 - 5
      dout = { << {4'b0001}}; if (dout != 4'b1000) $stop;
      dout = { << 2 {4'b0001}}; if (dout != 4'b0100) $stop;
      dout = { << 3 {4'b0001}}; if (dout != 4'b0010) $stop;
      dout = { << 4 {4'b0001}}; if (dout != 4'b0001) $stop;
      dout = { << 5 {4'b0001}}; if (dout != 4'b0001) $stop;

      // Stream operator: >>
      // Location: rhs of assignment
      //
      // Right-streaming operator on RHS does not reorder bits
      dout = { >> {4'b0001}}; if (dout != 4'b0001) $stop;
      dout = { >> 2 {4'b0001}}; if (dout != 4'b0001) $stop;
      dout = { >> 3 {4'b0001}}; if (dout != 4'b0001) $stop;
      dout = { >> 4 {4'b0001}}; if (dout != 4'b0001) $stop;
      dout = { >> 5 {4'b0001}}; if (dout != 4'b0001) $stop;

      // Stream operator: <<
      // Location: lhs of assignment
      { << {dout}} = 4'b0001; if (dout != 4'b1000) $stop;
      { << 2 {dout}} = 4'b0001; if (dout != 4'b0100) $stop;
      { << 3 {dout}} = 4'b0001; if (dout != 4'b0010) $stop;
      { << 4 {dout}} = 4'b0001; if (dout != 4'b0001) $stop;
      { << 5 {dout}} = 4'b0001; if (dout != 4'b0001) $stop;

      // Stream operator: >>
      // Location: lhs of assignment
      { >> {dout}} = 4'b0001; if (dout != 4'b0001) $stop;
      { >> 2 {dout}} = 4'b0001; if (dout != 4'b0001) $stop;
      { >> 3 {dout}} = 4'b0001; if (dout != 4'b0001) $stop;
      { >> 4 {dout}} = 4'b0001; if (dout != 4'b0001) $stop;
      { >> 5 {dout}} = 4'b0001; if (dout != 4'b0001) $stop;

      // Stream operator: <<
      // Location: lhs of assignment
      // RHS is *wider* than LHS
      /* verilator lint_off WIDTH */
      { << {dout}} = 5'b00001; if (dout != 4'b1000) $stop;
      { << 2 {dout}} = 5'b00001; if (dout != 4'b0100) $stop;
      { << 3 {dout}} = 5'b00001; if (dout != 4'b0010) $stop;
      { << 4 {dout}} = 5'b00001; if (dout != 4'b0001) $stop;
      { << 5 {dout}} = 5'b01101; if (dout != 4'b0110) $stop;
      /* verilator lint_on WIDTH */

      // Stream operator: >>
      // Location: lhs of assignment
      // RHS is *wider* than LHS
      /* verilator lint_off WIDTH */
      { >> {dout}} = 5'b01101; if (dout != 4'b0110) $stop;
      { >> 2 {dout}} = 5'b01101; if (dout != 4'b0110) $stop;
      { >> 3 {dout}} = 5'b01101; if (dout != 4'b0110) $stop;
      { >> 4 {dout}} = 5'b01101; if (dout != 4'b0110) $stop;
      { >> 5 {dout}} = 5'b01101; if (dout != 4'b0110) $stop;
      /* verilator lint_on WIDTH */

      // Stream operator: <<
      // Location: both sides of assignment
      { << {dout}} = { << {4'b0001}}; if (dout != 4'b0001) $stop;
      { << 2 {dout}} = { << 2 {4'b0001}}; if (dout != 4'b0001) $stop;
      { << 3 {dout}} = { << 3 {4'b0001}}; if (dout != 4'b0100) $stop;
      { << 4 {dout}} = { << 4 {4'b0001}}; if (dout != 4'b0001) $stop;
      { << 5 {dout}} = { << 5 {4'b0001}}; if (dout != 4'b0001) $stop;

      // Stream operator: <<
      // Location: as an operand within a statement
      //
      // Test slice sizes from 1 - 5
      if (4'({ << {4'b0001}}) != 4'b1000) $stop;
      if (4'({ << 2 {4'b0001}}) != 4'b0100) $stop;
      if (4'({ << 3 {4'b0001}}) != 4'b0010) $stop;
      if (4'({ << 4 {4'b0001}}) != 4'b0001) $stop;
      if (4'({ << 5 {4'b0001}}) != 4'b0001) $stop;

      // case
      dout32 = { << 3 { 32'b11010111000010100100010010010111 }}; if (dout32 != 32'he92910eb) $stop;
      dout11 = { << 4 { 11'b10010010111 }}; if (dout11 != 11'h3cc) $stop;
   end


   // The two always blocks below test run-time evaluation of the stream
   // operator in generated C code.
   //
   // Various stream operators are optimized away. Here's a brief summary:
   //
   //  Stream op on RHS of assign
   //  --------------------------
   //    X = { << a { Y } }  --- C function evaluates stream operator
   //                             -- if log2(a) == int  --> "fast" eval func
   //                             -- if log2(a) != int  --> "slow" eval func
   //    X = { >> a { Y } }  --- stream operator is optimized away
   //
   //  Stream op on LHS of assign
   //  --------------------------
   //  Note: if Y.width() > X.width, then the MSBs of Y are used, not the LSBs!
   //    { << a { X } } = Y  --- stream operator is moved to RHS, eval as above
   //    { >> a { X } } = Y  --- stream operator is optimized away

   logic [31:0]   din_i;
   logic [63:0]   din_q;
   logic [95:0]   din_w;

   // Stream op on RHS, left-stream operator
   logic [31:0]   dout_rhs_ls_i;
   logic [63:0]   dout_rhs_ls_q;
   logic [95:0]   dout_rhs_ls_w;

   // Stream op on RHS, right-stream operator
   logic [31:0]   dout_rhs_rs_i;
   logic [63:0]   dout_rhs_rs_q;
   logic [95:0]   dout_rhs_rs_w;

   // Stream op on both sides, left-stream operator
   logic [31:0]   dout_bhs_ls_i;
   logic [63:0]   dout_bhs_ls_q;
   logic [95:0]   dout_bhs_ls_w;

   // Stream op on both sides, right-stream operator
   logic [31:0]   dout_bhs_rs_i;
   logic [63:0]   dout_bhs_rs_q;
   logic [95:0]   dout_bhs_rs_w;

   // Stream operator on LHS (with concatenation on LHS)
   logic [3:0]    din_lhs;
   logic [1:0]    dout_lhs_ls_a, dout_lhs_ls_b;
   logic [1:0]    dout_lhs_rs_a, dout_lhs_rs_b;

   // Addition operator on LHS, right-shift tests:
   // Testing various shift sizes to exercise fast + slow funcs
   logic [22:0]   dout_rhs_ls_i_23_3;
   logic [22:0]   dout_rhs_ls_i_23_4;

   logic [36:0]   dout_rhs_ls_q_37_3;
   logic [36:0]   dout_rhs_ls_q_37_4;

   always @*
   begin
      // Stream operator: <<
      // Location: rhs of assignment
      //
      // Test each data type (I, Q, W)
      dout_rhs_ls_i = { << {din_i}};
      dout_rhs_ls_q = { << {din_q}};
      dout_rhs_ls_w = { << {din_w}};

      // Stream operator: >>
      // Location: rhs of assignment
      dout_rhs_rs_i = { >> {din_i}};
      dout_rhs_rs_q = { >> {din_q}};
      dout_rhs_rs_w = { >> {din_w}};

      // Stream operator: <<
      // Location: lhs of assignment
      { << 2 {dout_lhs_ls_a, dout_lhs_ls_b}} = din_lhs;

      // Stream operator: >>
      // Location: lhs of assignment
      { >> 2 {dout_lhs_rs_a, dout_lhs_rs_b}} = din_lhs;

      // Stream operator: <<
      // Location: both sides of assignment
      { << 5 {dout_bhs_ls_i}} = { << 5 {din_i}};
      { << 5 {dout_bhs_ls_q}} = { << 5 {din_q}};
      { << 5 {dout_bhs_ls_w}} = { << 5 {din_w}};

      // Stream operator: >>
      // Location: both sides of assignment
      { >> 5 {dout_bhs_rs_i}} = { >> 5 {din_i}};
      { >> 5 {dout_bhs_rs_q}} = { >> 5 {din_q}};
      { >> 5 {dout_bhs_rs_w}} = { >> 5 {din_w}};

      // Stream operator: <<
      // Location: both sides of assignment
      { << 5 {dout_bhs_ls_i}} = { << 5 {din_i}};
      { << 5 {dout_bhs_ls_q}} = { << 5 {din_q}};
      { << 5 {dout_bhs_ls_w}} = { << 5 {din_w}};

      // Stream operator: <<
      // Location: rhs of assignment
      //
      // Verify both fast and slow paths (fast: sliceSize = power of 2)
      dout_rhs_ls_i_23_3 = { << 3 {din_i[22:0]}}; // SLOW
      dout_rhs_ls_i_23_4 = { << 4 {din_i[22:0]}}; // FAST

      dout_rhs_ls_q_37_3 = { << 3 {din_q[36:0]}}; // SLOW
      dout_rhs_ls_q_37_4 = { << 4 {din_q[36:0]}}; // FAST
   end

   always @(posedge clk)
   begin
      if (cyc != 0) begin
         cyc <= cyc + 1;

         if (cyc == 1) begin
            din_i <= 32'h_00_00_00_01;
            din_q <= 64'h_00_00_00_00_00_00_00_01;
            din_w <= 96'h_00_00_00_00_00_00_00_00_00_00_00_01;

            din_lhs <= 4'b_00_01;
         end
         if (cyc == 2) begin
            din_i <= 32'h_04_03_02_01;
            din_q <= 64'h_08_07_06_05_04_03_02_01;
            din_w <= 96'h_0c_0b_0a_09_08_07_06_05_04_03_02_01;

            din_lhs <= 4'b_01_11;

            if (dout_rhs_ls_i != 32'h_80_00_00_00) $stop;
            if (dout_rhs_ls_q != 64'h_80_00_00_00_00_00_00_00) $stop;
            if (dout_rhs_ls_w != 96'h_80_00_00_00_00_00_00_00_00_00_00_00) $stop;

            if (dout_rhs_rs_i != 32'h_00_00_00_01) $stop;
            if (dout_rhs_rs_q != 64'h_00_00_00_00_00_00_00_01) $stop;
            if (dout_rhs_rs_w != 96'h_00_00_00_00_00_00_00_00_00_00_00_01) $stop;

            if (dout_lhs_ls_a != 2'b_01) $stop;
            if (dout_lhs_ls_b != 2'b_00) $stop;

            if (dout_lhs_rs_a != 2'b_00) $stop;
            if (dout_lhs_rs_b != 2'b_01) $stop;

            if (dout_bhs_rs_i != 32'h_00_00_00_01) $stop;
            if (dout_bhs_rs_q != 64'h_00_00_00_00_00_00_00_01) $stop;
            if (dout_bhs_rs_w != 96'h_00_00_00_00_00_00_00_00_00_00_00_01) $stop;

            if (dout_bhs_ls_i != 32'h_00_00_00_10) $stop;
            if (dout_bhs_ls_q != 64'h_00_00_00_00_00_00_01_00) $stop;
            if (dout_bhs_ls_w != 96'h_00_00_00_00_00_00_00_00_00_00_00_04) $stop;

            if (dout_rhs_ls_i_23_3 != 23'h_10_00_00) $stop;
            if (dout_rhs_ls_i_23_4 != 23'h_08_00_00) $stop;

            if (dout_rhs_ls_q_37_3 != 37'h_04_00_00_00_00) $stop;
            if (dout_rhs_ls_q_37_4 != 37'h_02_00_00_00_00) $stop;
         end
         if (cyc == 3) begin
            // The values below test the strange shift-merge done at the end of
            // the fast stream operators.
            // All-1s in the bits being streamed should end up as all-1s.
            din_i <= 32'h_00_7f_ff_ff;
            din_q <= 64'h_00_00_00_1f_ff_ff_ff_ff;

            if (dout_rhs_ls_i != 32'h_80_40_c0_20) $stop;
            if (dout_rhs_ls_q != 64'h_80_40_c0_20_a0_60_e0_10) $stop;
            if (dout_rhs_ls_w != 96'h_80_40_c0_20_a0_60_e0_10_90_50_d0_30) $stop;

            if (dout_rhs_rs_i != 32'h_04_03_02_01) $stop;
            if (dout_rhs_rs_q != 64'h_08_07_06_05_04_03_02_01) $stop;
            if (dout_rhs_rs_w != 96'h_0c_0b_0a_09_08_07_06_05_04_03_02_01) $stop;

            if (dout_bhs_ls_i != 32'h_40_30_00_18) $stop;
            if (dout_bhs_ls_q != 64'h_06_00_c1_81_41_00_c1_80) $stop;
            if (dout_bhs_ls_w != 96'h_30_2c_28_20_01_1c_1a_04_14_0c_00_06) $stop;

            if (dout_bhs_rs_i != 32'h_04_03_02_01) $stop;
            if (dout_bhs_rs_q != 64'h_08_07_06_05_04_03_02_01) $stop;
            if (dout_bhs_rs_w != 96'h_0c_0b_0a_09_08_07_06_05_04_03_02_01) $stop;

            if (dout_lhs_ls_a != 2'b_11) $stop;
            if (dout_lhs_ls_b != 2'b_01) $stop;

            if (dout_lhs_rs_a != 2'b_01) $stop;
            if (dout_lhs_rs_b != 2'b_11) $stop;

            if (dout_rhs_ls_i_23_3 != 23'h_10_08_c0) $stop;
            if (dout_rhs_ls_i_23_4 != 23'h_08_10_18) $stop;

            if (dout_rhs_ls_q_37_3 != 37'h_04_02_30_10_44) $stop;
            if (dout_rhs_ls_q_37_4 != 37'h_02_04_06_08_0a) $stop;
         end
         if (cyc == 4) begin
            if (dout_rhs_ls_i_23_3 != 23'h_7f_ff_ff) $stop;
            if (dout_rhs_ls_i_23_4 != 23'h_7f_ff_ff) $stop;

            if (dout_rhs_ls_q_37_3 != 37'h_1f_ff_ff_ff_ff) $stop;
            if (dout_rhs_ls_q_37_4 != 37'h_1f_ff_ff_ff_ff) $stop;
         end
         if (cyc == 9) begin
            $write("*-* All Finished *-*\n");
            $finish;
         end
      end
   end

endmodule
