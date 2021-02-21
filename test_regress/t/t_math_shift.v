// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2004 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Outputs
   ign, ign2, ign3, ign4, ign4s,
   // Inputs
   clk
   );

   input clk;
   output [31:0] ign;
   output [3:0]  ign2;
   output [11:0]  ign3;

   parameter [95:0] P6 = 6;
   localparam P64 = (1 << P6);

   // verilator lint_off WIDTH
   localparam [4:0] PBIG23 = 1'b1 << ~73'b0;
   localparam [3:0] PBIG29 = 4'b1 << 33'h100000000;
   // verilator lint_on WIDTH

   reg [31:0]           iright;
   reg signed [31:0]    irights;
   reg [31:0]           ileft;
   reg [P64-1:0]        qright;
   reg signed [P64-1:0] qrights;
   reg [P64-1:0]        qleft;
   reg [95:0]           wright;
   reg signed [95:0]    wrights;
   reg [95:0]           wleft;

   reg [31:0]           q_iright;
   reg signed [31:0]    q_irights;
   reg [31:0]           q_ileft;
   reg [P64-1:0]        q_qright;
   reg signed [P64-1:0] q_qrights;
   reg [P64-1:0]        q_qleft;
   reg [95:0]           q_wright;
   reg signed [95:0]    q_wrights;
   reg [95:0]           q_wleft;


   reg [31:0]           w_iright;
   reg signed [31:0]    w_irights;
   reg [31:0]           w_ileft;
   reg [P64-1:0]        w_qright;
   reg signed [P64-1:0] w_qrights;
   reg [P64-1:0]        w_qleft;
   reg [95:0]           w_wright;
   reg signed [95:0]    w_wrights;
   reg [95:0]           w_wleft;

   reg [31:0]           iamt;
   reg [63:0]           qamt;
   reg [95:0]           wamt;

   assign ign = {31'h0, clk} >>> 4'bx;  // bug760
   assign ign2 = {iamt[1:0] >> {22{iamt[5:2]}}, iamt[1:0] << (0 <<< iamt[5:2])}; // bug1174
   assign ign3 = {iamt[1:0] >> {22{iamt[5:2]}},
                  iamt[1:0] >> {11{iamt[5:2]}},
                  $signed(iamt[1:0]) >>> {22{iamt[5:2]}},
                  $signed(iamt[1:0]) >>> {11{iamt[5:2]}},
                  iamt[1:0] << {22{iamt[5:2]}},
                  iamt[1:0] << {11{iamt[5:2]}}};

   wire [95:0] wamtt = {iamt,iamt,iamt};
   output wire [95:0] ign4;
   assign ign4 = wamtt >> {11{iamt[5:2]}};
   output wire signed [95:0] ign4s;
   assign ign4s = $signed(wamtt) >>> {11{iamt[5:2]}};

   always @* begin
      iright  = 32'h819b018a >> iamt;
      irights = 32'sh819b018a >>> signed'(iamt);
      ileft   = 32'h819b018a << iamt;
      qright  = 64'hf784bf8f_12734089 >> iamt;
      qrights = 64'shf784bf8f_12734089 >>> signed'(iamt);
      qleft   = 64'hf784bf8f_12734089 << iamt;
      wright  = 96'hf784bf8f_12734089_190abe48 >> iamt;
      wrights = 96'shf784bf8f_12734089_190abe48 >>> signed'(iamt);
      wleft   = 96'hf784bf8f_12734089_190abe48 << iamt;

      q_iright  = 32'h819b018a >> qamt;
      q_irights = 32'sh819b018a >>> signed'(qamt);
      q_ileft   = 32'h819b018a << qamt;
      q_qright  = 64'hf784bf8f_12734089 >> qamt;
      q_qrights = 64'shf784bf8f_12734089 >>> signed'(qamt);
      q_qleft   = 64'hf784bf8f_12734089 << qamt;
      q_wright  = 96'hf784bf8f_12734089_190abe48 >> qamt;
      q_wrights = 96'shf784bf8f_12734089_190abe48 >>> signed'(qamt);
      q_wleft   = 96'hf784bf8f_12734089_190abe48 << qamt;

      w_iright  = 32'h819b018a >> wamt;
      w_irights = 32'sh819b018a >>> signed'(wamt);
      w_ileft   = 32'h819b018a << wamt;
      w_qright  = 64'hf784bf8f_12734089 >> wamt;
      w_qrights = 64'shf784bf8f_12734089 >>> signed'(wamt);
      w_qleft   = 64'hf784bf8f_12734089 << wamt;
      w_wright  = 96'hf784bf8f_12734089_190abe48 >> wamt;
      w_wrights = 96'shf784bf8f_12734089_190abe48 >>> signed'(wamt);
      w_wleft   = 96'hf784bf8f_12734089_190abe48 << wamt;
   end

   integer cyc; initial cyc=1;
   always @ (posedge clk) begin
      if (cyc!=0) begin
         cyc <= cyc + 1;
`ifdef TEST_VERBOSE
         $write("%d %x %x %x %x %x %x\n", cyc, ileft, iright, qleft, qright, wleft, wright);
`endif
         if (cyc==1) begin
            iamt <= 0;
            qamt <= 0;
            wamt <= 0;
            if (P64 != 64) $stop;
            if (5'b10110>>2  != 5'b00101) $stop;
            if (5'b10110>>>2 != 5'b00101) $stop;  // Note it cares about sign-ness
            if (5'b10110<<2  != 5'b11000) $stop;
            if (5'b10110<<<2 != 5'b11000) $stop;
            if (5'sb10110>>2  != 5'sb00101) $stop;
            if (5'sb10110>>>2 != 5'sb11101) $stop;
            if (5'sb10110<<2  != 5'sb11000) $stop;
            if (5'sb10110<<<2 != 5'sb11000) $stop;
            // Allow >64 bit shifts if the shift amount is a constant
            if ((64'sh458c2de282e30f8b >> 68'sh4) !== 64'sh0458c2de282e30f8) $stop;
         end
         if (cyc==2) begin
            iamt <= 28;
            qamt <= 28;
            wamt <= 28;
            if (ileft   != 32'h819b018a) $stop;
            if (iright  != 32'h819b018a) $stop;
            if (irights != 32'h819b018a) $stop;
            if (qleft   != 64'hf784bf8f_12734089) $stop;
            if (qright  != 64'hf784bf8f_12734089) $stop;
            if (qrights != 64'hf784bf8f_12734089) $stop;
            if (wleft   != 96'hf784bf8f12734089190abe48) $stop;
            if (wright  != 96'hf784bf8f12734089190abe48) $stop;
            if (wrights != 96'hf784bf8f12734089190abe48) $stop;
         end
         if (cyc==3) begin
            iamt <= 31;
            qamt <= 31;
            wamt <= 31;
            if (ileft  != 32'ha0000000) $stop;
            if (iright != 32'h8) $stop;
            if (irights != 32'hfffffff8) $stop;
            if (qleft  != 64'hf127340890000000) $stop;
            if (qright != 64'h0000000f784bf8f1) $stop;
            if (qrights != 64'hffffffff784bf8f1) $stop;
            if (wleft  != 96'hf12734089190abe480000000) $stop;
            if (wright != 96'h0000000f784bf8f127340891) $stop;
            if (wrights != 96'hffffffff784bf8f127340891) $stop;
         end
         if (cyc==4) begin
            iamt <= 32;
            qamt <= 32;
            wamt <= 32;
            if (ileft  != 32'h0) $stop;
            if (iright != 32'h1) $stop;
            if (qleft  != 64'h8939a04480000000) $stop;
            if (qright != 64'h00000001ef097f1e) $stop;
         end
         if (cyc==5) begin
            iamt <= 33;
            qamt <= 33;
            wamt <= 33;
            if (ileft  != 32'h0) $stop;
            if (iright != 32'h0) $stop;
            if (qleft  != 64'h1273408900000000) $stop;
            if (qright != 64'h00000000f784bf8f) $stop;
         end
         if (cyc==6) begin
            iamt <= 64;
            qamt <= 64;
            wamt <= 64;
            if (ileft  != 32'h0) $stop;
            if (iright != 32'h0) $stop;
            if (qleft  != 64'h24e6811200000000) $stop;
            if (qright != 64'h000000007bc25fc7) $stop;
         end
         if (cyc==7) begin
            iamt <= 128;
            qamt <= 128;
            wamt <= 128;
            if (ileft  != 32'h0) $stop;
            if (iright != 32'h0) $stop;
            if (qleft  != 64'h0) $stop;
            if (qright != 64'h0) $stop;
         end
         if (cyc==8) begin
            iamt <= 100;
            qamt <= {32'h10, 32'h0};
            wamt <= {32'h10, 64'h0};
            if (ileft   != '0) $stop;
            if (iright  != '0) $stop;
            if (irights != '1) $stop;
            if (qleft   != '0) $stop;
            if (qright  != '0) $stop;
            if (qrights != '1) $stop;
            if (wleft   != '0) $stop;
            if (wright  != '0) $stop;
            if (wrights != '1) $stop;
         end
         if (cyc==19) begin
            $write("*-* All Finished *-*\n");
            $finish;
         end

         // General rule to test all q's
         if (cyc != 0) begin
            if (ileft != q_ileft) $stop;
            if (iright != q_iright) $stop;
            if (irights != q_irights) $stop;
            if (qleft != q_qleft) $stop;
            if (qright != q_qright) $stop;
            if (qrights != q_qrights) $stop;
            if (wleft != q_wleft) $stop;
            if (wright != q_wright) $stop;
            if (wrights != q_wrights) $stop;

            if (ileft != w_ileft) $stop;
            if (iright != w_iright) $stop;
            if (irights != w_irights) $stop;
            if (qleft != w_qleft) $stop;
            if (qright != w_qright) $stop;
            if (qrights != w_qrights) $stop;
            if (wleft != w_wleft) $stop;
            if (wright != w_wright) $stop;
            if (wrights != w_wrights) $stop;
         end
      end
   end
endmodule
