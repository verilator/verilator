// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2014 by Wilson Snyder.

`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); fail='1; end while(0)
`define checkf(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); fail='1; end while(0)

module t (/*AUTOARG*/);

   bit fail;

   localparam signed [3:0] bug737_p1 = 4'b1000;

   wire [3:0] bug737_a = 4'b1010;
   reg [5:0]  bug737_y;
   reg signed [3:0] w4_s;
   reg signed [4:0] w5_s;
   reg [3:0] w4_u;
   reg [4:0] w5_u;
   reg signed [8:0] w9_s;
   real      r;
   initial begin
      // verilator lint_off WIDTH
      bug737_y = bug737_a + (bug737_p1 + 4'sb0);
      `checkh(bug737_y, 6'b010010);  //bug737

      //         6u     +[6u]   4s  +[6s] 6s
      bug737_y = 6'b001010 + (4'sb1000 + 6'sb0);
      `checkh(bug737_y, 6'b010010);  //bug737, getx 000010

      //         6u     +[6u]   4s  +[6s] 6s
      bug737_y = 6'b001010 + (4'b1000 + 6'sb0);
      `checkh(bug737_y, 6'b010010);  //ok

      bug737_y = 6'b001010 + (6'sb111000 + 6'sb0);
      `checkh(bug737_y, 6'b000010);  //ok

      //                       v--- sign extends to 6-bits
      bug737_y = 6'sb001010 + (4'sb1000 + 6'sb0);
      `checkh(bug737_y, 6'b000010);  //ok

      // From t_math_signed_3
      w4_s = 4'sb1111 - 1'b1;
      `checkh(w4_s,33'he);

      w4_s = 4'sb1111 - 5'b00001;
      `checkh(w4_s,33'he);

      w4_s = 4'sb1111 - 1'sb1;
      `checkh(w4_s,4'h0);
      w5_s = 4'sb1111 - 1'sb1;
      `checkh(w5_s,4'h0);

      w4_s = 4'sb1111 - 4'sb1111;
      `checkh(w4_s,4'h0);
      w5_s = 4'sb1111 - 4'sb1111;
      `checkh(w5_s,5'h0);

      // The assign LHS being signed or unsigned does not matter per IEEE
      // The upper add being signed DOES matter propagating to lower
      w4_s = 4'sb1111 - (1'sb1 + 4'b0);   //1'sb1 not extended as unsigned add
      `checkh(w4_s,4'he);
      w4_s = 4'sb1111 - (1'sb1 + 4'sb0);  //1'sb1 does sign extend
      `checkh(w4_s,4'h0);
      w4_s = 4'b1111 - (1'sb1 + 4'sb0);  //1'sb1 does *NOT* sign extend
      `checkh(w4_s,4'he);  // BUG, Verilator says 'h0

      w5_u = 4'b1111 + 4'b0001;  // Extends to 5 bits due to LHS
      `checkh(w5_u, 5'b10000);
      w4_u = 4'b1111 + 4'b0001;  // Normal case
      `checkh(w4_u, 4'b0000);

      // Another example of promotion, the add is 4 bits wide
      w4_u = 3'b111 + 3'b010;
      `checkh(w4_u, 4'b1001);
      //
      w4_u = 3'sb111 * 3'sb001; // Signed output, LHS does not matter
      `checkh(w4_u, 4'sb1111);
      w4_s = 3'sb111 * 3'sb001; // Signed output
      `checkh(w4_s, 4'sb1111);
      w4_s = 3'b111 * 3'sb001;  // Unsigned output
      `checkh(w4_s, 4'b0111);

      // Conditionals get width from parent; are assignment-like
      w4_u = 1'b0 ? 4'b0 : (2'b01+2'b11);
      `checkh(w4_u, 4'b0100);
      w4_u = 1'b0 ? 4'b0 : (6'b001000+6'b001000);
      `checkh(w4_u, 4'b0000);

      // If RHS is larger, that larger size is used
      w4_u = 5'b10000 / 5'b00100;
      `checkh(w4_u, 4'b0100);

      // bug754
      w5_u = 4'sb0010 << -2'sd1;  // << 3
`ifdef VCS
      `checkh(w5_u, 5'b00000);  // VCS E-2014.03 bug
`else
      `checkh(w5_u, 5'b10000);  // VCS E-2014.03 bug
`endif
      w5_u = 4'sb1000 << 0;   // Sign extends
      `checkh(w5_u, 5'b11000);

      // Reals do not propagate to children
      r = 1.0 + ( 1 + (1 / 2));
      `checkf(r, 2.0);

      // Self determined sign extension
      r = $itor(3'sb111);
      `checkf(r, -1.0);

      // If any part of case is real, all is real
      case (22)
	22.0: ;
	22.1: $stop;
	default: $stop;
      endcase

      // bug759
      w5_u = { -4'sd7 };
      `checkh(w5_u, 5'b01001);
      w5_u = {2{ -2'sd1 }};
      `checkh(w5_u, 5'b01111);
      // Don't break concats....
      w5_u = {{0{1'b1}}, -4'sd7 };
      `checkh(w5_u, 5'b01001);
      w9_s = { -4'sd7, -4'sd7 };
      `checkh(w9_s, 9'b010011001);
      {w5_u, {w4_u}} = 9'b10101_1100;
      `checkh(w5_u, 5'b10101);
      `checkh(w4_u, 4'b1100);
      {w4_u} = 4'b1011;
      `checkh(w4_u, 4'b1011);

      if (fail) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
