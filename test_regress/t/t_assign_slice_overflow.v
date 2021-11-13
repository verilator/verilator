// DESCRIPTION: Test that slice assignment overflows are handled correctly,
// i.e. that if you assign to a slice such that some of the bits you assign to
// do not actually exist, that those bits get correctly discarded.
// Issue #2803 existed in a number number of different codepaths in
// verilated.h and V3Expand.cpp.  This test should cover all of these cases
// when run both with and without the -Ox flag to verilator.
//  - Select offset constant, insert IData into CData
//  - Select offset constant, insert IData into SData
//  - Select offset constant, insert IData into IData
//  - Select offset constant, insert QData into QData
//  - Select offset constant, insert IData into WData within a word
//  - Select offset constant, insert IData into WData crossing a word boundary
//  - Select offset constant, insert IData into WData whole word insertion
//  - Select offset constant, insert QData into WData
//  - Select offset constant, insert WData into WData, several whole words
//  - Select offset constant, insert WData into WData, starting at word-offset
//  - Select offset constant, insert WData into WData, all other cases
//  - Select offset is non-constant, destination is wide, bit-select width == 1
//  - Select offset is non-constant, destination is wide, bit-select width != 1
//  - Select offset is non-constant, destination is narrow
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 by David Turner.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer cyc = 0;
   // Non-constant offsets
   reg        varoffset1;
   reg [6:0]  varoffset2;
   reg [6:0]  varoffset3;

   // Destinations for variable-offset assignments
   reg [69:0] dstwide1;
   reg [69:0] dstwide2;
   reg [1:0] dstnarrow;

   // Constant offsets
   reg [6:0] constoffset;

   // Destinations for constant-offset assignments
   reg [2:0]  dst_cdata;
   reg [11:0] dst_sdata;
   reg [29:0] dst_idata;
   reg [59:0] dst_qdata;
   reg [69:0] dst_wdata1; // assign idata within word
   reg [69:0] dst_wdata2; // assign idata crossing word boundary
   reg [69:0] dst_wdata3; // assign idata corresponding to whole word
   reg [69:0] dst_wdata4; // assign qdata
   reg [69:0] dst_wdata5; // assign wdata corresponding to several whole words
   reg [69:0] dst_wdata6; // assign wdata starting at word-offset
   reg [69:0] dst_wdata7; // assign wdata unaligned

   always @(*) begin
      // Non-constant select offset, destination narrow
      dstnarrow = 2'd0;
      dstnarrow[varoffset1 +: 2'd2] = 2'd2;

      // Non-constant select offset, destination wide, width == 1
      dstwide1 = 70'd0;
      dstwide1[varoffset2 +: 1'd1] = 1'd1;

      // Non-constant select offset, destination wide, width != 1
      dstwide2 = 70'd0;
      dstwide2[varoffset3 +: 2'd2] = 2'd2;

      // Constant offset, IData into CData
      constoffset = 7'd2;
      dst_cdata = 3'd0;
      dst_cdata[constoffset[0 +: 2] +: 3'd3] = 3'd6;

      // Constant offset, IData into SData
      constoffset = 7'd11;
      dst_sdata = 12'd0;
      dst_sdata[constoffset[0 +: 4] +: 2'd2] = 2'd2;

      // Constant offset, IData into IData
      constoffset = 7'd29;
      dst_idata = 30'd0;
      dst_idata[constoffset[0 +: 5] +: 2'd2] = 2'd2;

      // Constant offset, QData into QData
      constoffset = 7'd59;
      dst_qdata = 60'd0;
      dst_qdata[constoffset[0 +: 6] +: 2'd2] = 2'd2;

      // Constant offset, IData into WData within word
      constoffset = 7'd69;
      dst_wdata1 = 70'd0;
      dst_wdata1[constoffset +: 2'd2] = 2'd2;

      // Constant offset, IData into WData crossing word boundary
      constoffset = 7'd61;
      dst_wdata2 = 70'd0;
      dst_wdata2[constoffset +: 4'd10] = 10'd1 << 4'd9;

      // Constant offset, IData into WData replacing a whole word
      constoffset = 7'd64;
      dst_wdata3 = 70'd0;
      dst_wdata3[constoffset +: 6'd32] = 32'd1 << 3'd6;

      // Constant offset, QData into WData
      constoffset = 7'd31;
      dst_wdata4 = 70'd0;
      dst_wdata4[constoffset +: 7'd40] = 40'd1 << 7'd39;

      // Constant offset, WData into WData replacing whole words
      constoffset = 7'd32;
      dst_wdata5 = 70'd0;
      dst_wdata5[constoffset +: 7'd64] = 64'd1 << 7'd38;

      // Constant offset, WData into WData offset word aligned
      constoffset = 7'd32;
      dst_wdata6 = 70'd0;
      dst_wdata6[constoffset +: 7'd40] = 40'd1 << 7'd38;

      // Constant offset, WData into WData unaligned
      constoffset = 7'd1;
      dst_wdata7 = 70'd0;
      dst_wdata7[constoffset +: 7'd70] = 70'd1 << 7'd69;
   end

   // Test loop
   always @ (posedge clk) begin
      // State machine to avoid verilator constant-folding offset
      if (cyc == 0) begin
         // Initialisation
         varoffset1 <= 1'd0;
         varoffset2 <= 7'd0;
         varoffset3 <= 7'd0;
      end else if (cyc == 1) begin
         // Variable offsets set here to avoid verilator constant folding
         varoffset1 <= 1'd1;
         varoffset2 <= 7'd70;
         varoffset3 <= 7'd69;
      end else if (cyc == 2) begin
         // Check all destinations are 0
         $write("dstwide1   = %23d, downshifted = %23d\n", dstwide1, dstwide1 >> 1);
         $write("dstwide2   = %23d, downshifted = %23d\n", dstwide2, dstwide2 >> 1);
         $write("dstnarrow  = %23d, downshifted = %23d\n", dstnarrow, dstnarrow >> 1);
         $write("dst_cdata  = %23d, downshifted = %23d\n", dst_cdata, dst_cdata >> 1);
         $write("dst_sdata  = %23d, downshifted = %23d\n", dst_sdata, dst_sdata >> 1);
         $write("dst_idata  = %23d, downshifted = %23d\n", dst_idata, dst_idata >> 1);
         $write("dst_qdata  = %23d, downshifted = %23d\n", dst_qdata, dst_qdata >> 1);
         $write("dst_wdata1 = %23d, downshifted = %23d\n", dst_wdata1, dst_wdata1 >> 1);
         $write("dst_wdata2 = %23d, downshifted = %23d\n", dst_wdata2, dst_wdata2 >> 1);
         $write("dst_wdata3 = %23d, downshifted = %23d\n", dst_wdata3, dst_wdata3 >> 1);
         $write("dst_wdata4 = %23d, downshifted = %23d\n", dst_wdata4, dst_wdata4 >> 1);
         $write("dst_wdata5 = %23d, downshifted = %23d\n", dst_wdata5, dst_wdata5 >> 1);
         $write("dst_wdata6 = %23d, downshifted = %23d\n", dst_wdata6, dst_wdata6 >> 1);
         $write("dst_wdata7 = %23d, downshifted = %23d\n", dst_wdata7, dst_wdata7 >> 1);

         if (dstwide1 !== 70'd0 || (dstwide1 >> 1) !== 70'd0) $stop;
         if (dstwide2 !== 70'd0 || (dstwide2 >> 1) !== 70'd0) $stop;
         if (dstnarrow !== 2'd0 || (dstnarrow >> 1) !== 2'd0) $stop;
         if (dst_cdata !== 3'd0 || (dst_cdata >> 1) !== 3'd0) $stop;
         if (dst_sdata !== 12'd0 || (dst_sdata >> 1) !== 12'd0) $stop;
         if (dst_idata !== 30'd0 || (dst_idata >> 1) !== 30'd0) $stop;
         if (dst_qdata !== 60'd0 || (dst_qdata >> 1) !== 60'd0) $stop;
         if (dst_wdata1 !== 70'd0 || (dst_wdata1 >> 1) !== 70'd0) $stop;
         if (dst_wdata2 !== 70'd0 || (dst_wdata2 >> 1) !== 70'd0) $stop;
         if (dst_wdata3 !== 70'd0 || (dst_wdata3 >> 1) !== 70'd0) $stop;
         if (dst_wdata4 !== 70'd0 || (dst_wdata4 >> 1) !== 70'd0) $stop;
         if (dst_wdata5 !== 70'd0 || (dst_wdata5 >> 1) !== 70'd0) $stop;
         if (dst_wdata6 !== 70'd0 || (dst_wdata6 >> 1) !== 70'd0) $stop;
         if (dst_wdata7 !== 70'd0 || (dst_wdata7 >> 1) !== 70'd0) $stop;
      end else begin
         $write("*-* All Finished *-*\n");
         $finish;
      end

      cyc <= cyc + 1;
   end
endmodule
