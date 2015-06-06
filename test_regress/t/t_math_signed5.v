// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2014 by Wilson Snyder.

`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); fail='1; end while(0)
`define checkf(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); fail='1; end while(0)
`ifdef VERILATOR
 `define c(v,vs) ($c(vs))  // Don't constify a value
`else
 `define c(v,vs) (v)
`endif

   module t (/*AUTOARG*/
   // Outputs
   ow4_u
   );

   bit fail;

   reg signed [3:0] w4_s;
   reg signed [4:0] w5_s;
   reg [2:0] 	    w3_u;
   reg [3:0] 	    w4_u;
   reg [4:0] 	    w5_u;
   reg [5:0] 	    w6_u;
   reg [15:0] 	    w16a_u;
   reg [15:0] 	    w16_u;
   reg [31:0] 	    w32_u;
   real 	    r;

   reg signed [4:0] bug754_a;

   integer 	    i;

   //verilator lint_off WIDTH
   wire a = (5'b0 == (5'sb11111 >>> 3'd7));
   wire b = (5'sb11111 == (5'sb11111 >>> 3'd7));
   wire c = (1'b0+(5'sb11111 >>> 3'd7));
   wire d = (1'sb0+(5'sb11111 >>> 3'd7));
   wire e = (5'b0 == (5'sb11111 / 5'sd3));
   wire f = (5'sb0 == (5'sb11111 / 5'sd3));
   wire g = (5'b01010 == (5'b11111 / 5'sd3));
   initial begin
      // verilator lint_off STMTDLY
      #1;
`ifdef VCS  // I-2014.03
      `checkh({a, b, c, d, e, f, g}, 7'b1101111);
`else
      `checkh({a, b, c, d, e, f, g}, 7'b1101011);
`endif

      //======================================================================

      if ((-1 >>> 3) != -1) $stop;	// Decimals are signed

      i = 3'sb111 >>> 3;
      `checkh(i, -1);
      i = -1 >>> 3;
      `checkh(i, -1);

      bug754_a = -1;
      w4_u = |0 != (bug754_a >>> 3'd7);
      `checkh(w4_u, 4'b0);

      // Sanity check: -1>>7 == -1
      w5_u = (5'sb11111 >>> 3'd7);
      `checkh(w5_u, 5'b11111);

      // bug756
      w4_u = (5'b0 == (5'sb11111 >>> 3'd7));
      `checkh(w4_u, 4'b0001);
      w4_u = ((5'b0 == (5'sb11111 >>> 3'd7)));   // Exp 0     Vlt 0
      `checkh(w4_u, 4'b0001);
      w4_u = ((5'b01111 == (5'sb11111 / 5'sd2)));    // Strength-reduces to >>>
`ifdef VCS  // I-2014.03
      `checkh(w4_u, 4'b0000);  // Wrong, gets 5'b0==..., unsigned does not propagate
`else
      `checkh(w4_u, 4'b0001);  // NC-Verilog, Modelsim, XSim, ...
`endif

      // Does == sign propagate from lhs to rhs?  Yes, but not in VCS
      w4_u = ((5'b01010 == (5'sb11111 / 5'sd3)));    // Exp 0     Vlt 0  // Must be signed result (-1/3) to make this result zero
`ifdef VCS  // I-2014.03
      `checkh(w4_u, 4'b0000);  // Wrong, gets 5'b0==..., unsigned does not propagate
`else
      `checkh(w4_u, 4'b0001);  // NC-Verilog, Modelsim, XSim, ...
`endif

      w4_u = (1'b0+(5'sb11111 >>> 3'd7));        // Exp 00000 Vlt 000000 Actually the signedness of result does NOT matter
      `checkh(w4_u, 4'b0000);

      w4_u = (5'sb0 == (5'sb11111 / 5'sd3));  // Must be signed result (-1/3) to make this result zero
      `checkh(w4_u, 4'b0001);
      // Does == width propagate from lhs to rhs? Yes
      w4_u = (3'b100==(3'b111 << 2));
      `checkh(w4_u, 4'b0001);
      w4_u = (4'b100==(3'b111 << 2));
      `checkh(w4_u, 4'b0000);
      w4_u = (4'b1100==(3'b111 << 2));
      `checkh(w4_u, 4'b0001);

      // Does >>> sign propagate from input same as for +? Yes
      w4_u = (1'b0+(5'sb11111 >>> 3'd7));
      `checkh(w4_u, 4'b0000);
      w4_u = (1'sb0+(5'sb11111 >>> 3'd7));
      `checkh(w4_u, 4'b1111);

      // Does << width propagate from input same as for +? Yes
      w4_u = (3'b0+(3'b111 << 2));
      `checkh(w4_u, 4'b1100);  // width 4 =='s LHS
      w4_u = (4'b0+(3'b111 << 2));
      `checkh(w4_u, 4'b1100);

      w4_u = (5'sb11111 == (5'sb11111 >>> 3'd7));  // WHAT? Signedness does propagate across ==?????
      `checkh(w4_u, 4'b0001);
      w4_u = ((5'b0 == (5'sb11111 >>> 3'd7)));
      `checkh(w4_u, 4'b0001);

      // bug756
      w5_s = -1;
      w3_u = 7;
      w4_u = |0 != (w5_s >>> w3_u);
      `checkh(w4_u, 4'b0000);

      // bug763
      w3_u = 2;
      w4_u = (w3_u >> 2'b11) >> 1;
      `checkh(w4_u, 4'b0000);

      // bug766
      w16a_u = 16'h1234;
      w16_u = (w16a_u >> 16) >>> 32'h7ffffff1;
      `checkh(w16_u, 16'h0000);

      // bug768
      w4_s = 4'sd4;
      w4_u = $signed(5'd1 > w4_s-w4_s);
      `checkh(w4_u, 4'b1111);
      w4_s = `c(4,"4");  // Eval at runtime
      w4_u = $signed(5'd1 > w4_s-w4_s);
      `checkh(w4_u, 4'b1111);

      // bug772
      w4_s = w4_u << 1 <<< 0/0;
`ifndef VERILATOR       // In v4 can't check value as not 4-state
      `checkh(w4_s, 4'bxxxx);
`endif

      // bug773
      w5_u = `c(31, 31);
      w5_s = w5_u >> ((w5_u ? 1 : 2) << w5_u);
      `checkh(w5_s, 5'b0);

      // bug774
      w4_u = `c(4, 5);
      w6_u = `c(6, 35);
      w4_u = 64'd0 | (w4_u << w6_u);
      `checkh(w4_u, 0);

      // bug776
      w4_u = `c(4, 1);
      w4_u = (w4_u >> w4_u) ^~ (w4_u >> w4_u);
      `checkh(w4_u, 4'b1111);

      // bug828
      // verilator lint_off WIDTH
      w32_u = 32'(signed'({4'b0001,5'b10000}) << 3);
      `checkh(w32_u, 32'h0000_0180);
      w32_u = 32'(signed'({4'b0011,5'b10000}) << 3);
      `checkh(w32_u, 32'h0000_0380);
      w32_u = signed'(32'({4'b0001,5'b10000}) << 3);
      `checkh(w32_u, 32'h0000_0180);
      w32_u = signed'(32'({4'b0011,5'b10000}) << 3);
      `checkh(w32_u, 32'h0000_0380);
      // verilator lint_on WIDTH
      w32_u = 32'(signed'({4'b0011,5'b10000})) << 3;  // Check no width warning
      `checkh(w32_u, 32'h0000_0380);

      if (fail) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

   // bug775
   output [3:0]     ow4_u;  // Must be consumed
   assign  ow4_u = ((0/0) ? 1 : 2) % 0;

endmodule
