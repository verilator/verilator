// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 Yutetsu TAKATSUKASA.
// SPDX-License-Identifier: CC0-1.0

// This function always returns 0, so safe to take bitwise OR with any value.
// Calling this function stops constant folding as Verialtor does not know
// what this function returns.
import "DPI-C" context function int c_fake_dependency();

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer cyc = 0;
   reg [63:0] crc;
   reg [63:0] sum;

   // Take CRC data and apply to testblock inputs
   wire [31:0] in = crc[31:0];

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   logic                o;                     // From test of Test.v
   // End of automatics

   wire [31:0]          i = crc[31:0];

   Test test(/*AUTOINST*/
             // Outputs
             .o                         (o),
             // Inputs
             .clk                       (clk),
             .i                         (i[31:0]));

   // Aggregate outputs into a single result vector
   wire [63:0] result = {63'b0, o};

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d crc=%x result=%x\n", $time, cyc, crc, result);
      $display("o %b", o);
`endif
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
      sum <= result ^ {sum[62:0], sum[63] ^ sum[2] ^ sum[0]};
      if (cyc == 0) begin
         // Setup
         crc <= 64'h5aef0c8d_d70a4497;
         sum <= '0;
      end
      else if (cyc < 10) begin
         sum <= '0;
      end
      else if (cyc < 99) begin
      end
      else begin
         $write("[%0t] cyc==%0d crc=%x sum=%x\n", $time, cyc, crc, sum);
         if (crc !== 64'hc77bb9b3784ea091) $stop;
         // What checksum will we end up with (above print should match)
`define EXPECTED_SUM 64'h4c5aa8d19cd13750

         if (sum !== `EXPECTED_SUM) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule

module Test(/*AUTOARG*/
   // Outputs
   o,
   // Inputs
   clk, i
   );

   input clk;
   input [31:0] i;
   logic [31:0] d;
   logic d0, d1, d2, d3, d4, d5, d6, d7;
   logic bug3182_out;
   logic bug3197_out;
   logic bug3445_out;
   logic bug3470_out;
   logic bug3509_out;
   wire  bug3399_out0;
   wire  bug3399_out1;
   logic bug3786_out;
   logic bug3824_out;
   logic bug4059_out;
   logic bug4832_out;
   logic bug4837_out;
   logic bug4857_out;
   logic bug4864_out;

   output logic o;

   logic [18:0] tmp;
   assign o = ^tmp;

   always_ff @(posedge clk) begin
      d <= i;
      d0 <= i[0];
      d1 <= i[1];
      d2 <= i[2];
      d3 <= i[3];
      d4 <= i[4];
      d5 <= i[5];
      d6 <= i[6];
      d7 <= i[7];
   end
   always_ff @(posedge clk) begin
      // Cover more lines in V3Const.cpp
      tmp[0] <= (d0 || (!d0 && d1)) ^ ((!d2 && d3) || d2); // maatchOrAndNot()
      tmp[1] <= ((32'd2 ** i) & 32'h10) == 32'b0;  // replacePowShift
      tmp[2] <= ((d0 & d1) | (d0 & d2))^ ((d3 & d4) | (d5 & d4));  // replaceAndOr()
      tmp[3] <= d0 <-> d1; // replaceLogEq()
      tmp[4] <= i[0] & (i[1] & (i[2] & (i[3] | d[4])));  // ConstBitOpTreeVisitor::m_frozenNodes
      tmp[5] <= bug3182_out;
      tmp[6] <= bug3197_out;
      tmp[7] <= bug3445_out;
      tmp[8] <= bug3470_out;
      tmp[9] <= bug3509_out;
      tmp[10]<= bug3399_out0;
      tmp[11]<= bug3399_out1;
      tmp[12]<= bug3786_out;
      tmp[13]<= bug3824_out;
      tmp[14]<= bug4059_out;
      tmp[15]<= bug4832_out;
      tmp[16]<= bug4837_out;
      tmp[17]<= bug4857_out;
      tmp[18]<= bug4864_out;
   end

   bug3182 i_bug3182(.in(d[4:0]), .out(bug3182_out));
   bug3197 i_bug3197(.clk(clk), .in(d), .out(bug3197_out));
   bug3445 i_bug3445(.clk(clk), .in(d), .out(bug3445_out));
   bug3470 i_bug3470(.clk(clk), .in(d), .out(bug3470_out));
   bug3509 i_bug3509(.clk(clk), .in(d), .out(bug3509_out));
   bug3399 i_bug3399(.clk(clk), .in(d), .out0(bug3399_out0), .out1(bug3399_out1));
   bug3786 i_bug3786(.clk(clk), .in(d), .out(bug3786_out));
   bug3824 i_bug3824(.clk(clk), .in(d), .out(bug3824_out));
   bug4059 i_bug4059(.clk(clk), .in(d), .out(bug4059_out));
   bug4832 i_bug4832(.clk(clk), .in(d), .out(bug4832_out));
   bug4837 i_bug4837(.clk(clk), .in(d), .out(bug4837_out));
   bug4857 i_bug4857(.clk(clk), .in(d), .out(bug4857_out));
   bug4864 i_bug4864(.clk(clk), .in(d), .out(bug4864_out));

endmodule

module bug3182(in, out);
   input wire [4:0] in;
   output wire out;

   logic [4:0] bit_source;

   /* verilator lint_off WIDTH */
   always @(in)
      bit_source = c_fake_dependency() | in;

   wire [5:0] tmp = bit_source; // V3Gate should inline this
   assign out =  ~(tmp >> 5) & (bit_source == 5'd10);
   /* verilator lint_on WIDTH */
endmodule

module bug3197(input wire clk, input wire [31:0] in, output out);
   logic [63:0] d;
   always_ff @(posedge clk)
      d <= {d[31:0], in[0] ? in : 32'b0};

   wire tmp0 = (|d[38:0]);
   assign out = (d[39] | tmp0);
endmodule


// See issue #3445
// An unoptimized node is kept as frozen node, but its LSB and polarity were not saved.
// AST of RHS of result0 looks as below:
//   AND(SHIFTR(AND(WORDSEL(ARRAYSEL(VARREF)), WORDSEL(ARRAYSEL(VARREF)))), 32'd11)
//                  ~~~~~~~~~~~~~~~~~~~~~~~~~  ~~~~~~~~~~~~~~~~~~~~~~~~~
// Two of WORDSELs are frozen nodes. They are under SHIFTR of 11 bits.
//
// Fixing issue #3445 needs to
//  1. Take AstShiftR and AstNot into op count when diciding optimizable or not
//     (result0 and result2 in the test)
//  2. Insert AstShiftR if LSB of the frozen node is not 0 (result1 in the test)
//  3. Insert AstNot if polarity of the frozen node is false (resutl3 in the
//  test)
module bug3445(input wire clk, input wire [31:0] in, output wire out);
   logic [127:0] d;
   always_ff @(posedge clk)
      d <= {d[95:0], in};

   typedef struct packed {
      logic        a;
      logic [ 2:0] b;
      logic [ 2:0] c;
      logic [ 1:0] d;
      logic [ 7:0] e;
      logic [31:0] f;
      logic [ 3:0] g;
      logic [31:0] h;
      logic        i;
      logic [41:0] j;
   } packed_struct;
   packed_struct st[4];

   // This is always 1'b0, but Verilator cannot notice it.
   // This signal helps to reveal wrong optimization of result2 and result3.
   logic zero;
   always_ff @(posedge clk) begin
      st[0] <= d;
      st[1] <= st[0];
      st[2] <= st[1];
      st[3] <= st[2];
      zero <= c_fake_dependency() > 0;
   end

   logic result0, result1, result2, result3;
   always_ff @(posedge clk) begin
      // Cannot optimize further.
      result0 <= (st[0].g[0] & st[0].h[0]) & (in[0] == 1'b0);
      // There are redundant !in[0] terms. They should be simplified.
      result1 <= (!in[0] & (st[1].g[0] & st[1].h[0])) & ((in[0] == 1'b0) & !in[0]);
      // Cannot optimize further.
      result2 <= !(st[2].g[0] & st[2].h[0]) & (zero == 1'b0);
      // There are redundant zero terms. They should be simplified.
      result3 <= (!zero & !(st[3].g[0] & st[3].h[0])) & ((zero == 1'b0) & !zero);
   end

   assign out = result0 ^ result1 ^ (result2 | result3);
endmodule

// Bug3470
// CCast had been ignored in bit op tree optimization
// Assume the following HDL input:
//     (^d[38:32]) ^ (^d[31:0])
//     where d is logic [38:0]
// ^d[31:0] becomes REDXOR(CCast(uint32_t, d)),
// but CCast was ignored and interpreted as ^d[38:0].
// Finally (^d[38:32]) ^ (^d31:0]) was wrongly transformed to
// (^d[38:32]) ^ (^d[38:0])
//   ->  (^d[38:32]) ^ ((^d[38:32]) ^ (^d[31:0]))
//   -> ^d[31:0]
// Of course the correct result is ^d[38:0] = ^d
module bug3470(input wire clk, input wire [31:0] in, output wire out);
   logic [38:0] d;
   always_ff @(posedge clk)
      d <= {d[6:0], in};

   logic tmp, expected;
   always_ff @(posedge clk) begin
     tmp <= ^(d >> 32) ^ (^d[31:0]);
     expected <= ^d;
   end

   always @(posedge clk)
      if (tmp != expected) $stop;

   assign out = tmp;
endmodule

// Bug3509
// Only bit range of "var" was considered in
// "comp == (mask & var)"
//   and
// "comp != (mask & var)"
//
// It caused wrong result if "comp" has wider bit width because
// upper bit of "comp" was ignored.
//
// If "comp" has '1' in upper bit range than "var",
// the result is constant after optimization.
module bug3509(input wire clk, input wire [31:0] in, output reg out);
   reg [2:0] r0;
   always_ff @(posedge clk)
      r0 <= in[2:0];

   wire [3:0] w1_0 = {1'b0, in[2:0]};
   wire [3:0] w1_1 = {1'b0, r0};

   wire tmp[4];

   // tmp[0:1] is always 0 because w1[3] == 1'b0
   // tmp[2:3] is always 1 because w1[3] == 1'b0
   assign tmp[0] = w1_0[3:2] == 2'h2 && w1_0[1:0] != 2'd3;
   assign tmp[1] = w1_1[3:2] == 2'h2 && w1_1[1:0] != 2'd3;
   assign tmp[2] = w1_0[3:2] != 2'h2 || w1_0[1:0] == 2'd3;
   assign tmp[3] = w1_1[3:2] != 2'h2 || w1_1[1:0] == 2'd3;
   always_ff @(posedge clk) begin
      out <= tmp[0] | tmp[1] | !tmp[2] | !tmp[3];
   end

   always @(posedge clk) begin
      if(tmp[0]) begin
         $display("tmp[0] != 0");
         $stop;
      end
      if(tmp[1]) begin
         $display("tmp[1] != 0");
         $stop;
      end
      if(!tmp[2]) begin
         $display("tmp[2] != 1");
         $stop;
      end
      if(!tmp[3]) begin
         $display("tmp[3] != 1");
         $stop;
      end
   end
endmodule

// Bug3399
// replaceShiftSame() in V3Const.cpp optimizes
// Or(Shift(ll,CONSTlr),Shift(rl,CONSTrr==lr)) -> Shift(Or(ll,rl),CONSTlr)
// (Or/And may also be reversed)
//
// dtype of Or after the transformation must be as same as ll and rl, but was dtype of Or BEFORE transformation.
// When the result of Shift was 1 bit width, bit op tree optimization
// optimized the tree even though the graph needs more width.
// Remember that the target of bit op tree optimization is 1 bit width.
module bug3399(input wire clk, input wire [31:0] in, inout wire out0, inout wire out1);
   logic [1:0] driver = '0;
   logic [1:0] d;
   always_ff @(posedge clk) begin
      driver <= 2'b11;
      d <= in[1:0];
   end

   assign out0 = driver[0] ? d[0] : 1'bz;
   assign out1 = driver[1] ? d[1] : 1'bz;
endmodule

// Bug3786
// When V3Expand is skipped, wide number is not split by WORDSEL.
// Bit op tree opt. expects that bit width is 64 bit at most.
module bug3786(input wire clk, input wire [31:0] in, inout wire out);
   logic [127:0] d0, d1;
   always_ff @(posedge clk) begin
      d0 <= {d0[127:32], in};
      d1 <= d1;
   end

   assign out = ^{d1, d0};
endmodule

// Bug3824
// When a variable is shift-out, the term becomes 0.
// Such behavior was not considered in Or-tree.
module bug3824(input wire clk, input wire [31:0] in, output wire out);
   logic [5:0] a;
   always_ff @(posedge clk) a <= in[5:0];
   logic [6:0] b;
   assign b = {1'b0, a};

   logic c_and;
   assign c_and = (b[6]);  // c_and is always 1'b0
   always_comb if (c_and != 1'b0) $stop;
   logic d_and;
   always_ff @(posedge clk) d_and <= (&a) & c_and;

   logic c_or;
   assign c_or = ~(b[6]);  // c_or is always 1'b1 as b[6] is 1'b0
   always_comb if (c_or != 1'b1) $stop;
   logic d_or;
   always_ff @(posedge clk) d_or <= (|a) | c_or;

   logic c_xor;
   assign c_xor = ^(b[6]);  // c_xor is always 1'b0
   always_comb if (c_xor != 1'b0) $stop;
   logic d_xor;
   always_ff @(posedge clk) d_xor <= (^a) ^ c_xor;

  assign out = d_and ^ d_or ^ d_xor;
endmodule

/// See issue #4059
// Frozen node in an xor tree held unnecessary poloarity.
// In an XOR tree, the entire result is flipped if necessary according to
// total polarity. This bug was introduced when fixing issue #3445.
module bug4059(input wire clk, input wire [31:0] in, output wire out);
   wire [127:0] words_i;
   for (genvar i = 0; i < $bits(in); ++i) begin
      always_ff @(posedge clk)
         words_i[4 * i +: 4] <= {4{in[i]}};
   end

   wire _000_ = ~(words_i[104] ^ words_i[96]);
   wire _001_ = ~(words_i[88] ^ words_i[80]);
   wire _002_ = ~(_000_ ^ _001_);
   wire _003_ = words_i[72] ^ words_i[64];
   wire _004_ = words_i[120] ^ words_i[112];
   wire _005_ = ~(_003_ ^ _004_);
   wire _006_ = ~(_002_ ^ _005_);
   wire _007_ = words_i[40] ^ words_i[32];
   wire _008_ = ~(words_i[24] ^ words_i[16]);
   wire _009_ = ~(_007_ ^ _008_);
   wire _010_ = words_i[8] ^ words_i[0];
   wire _011_ = words_i[56] ^ words_i[48];
   wire _012_ = ~(_010_ ^ _011_);
   wire _013_ = ~(_009_ ^ _012_);
   assign out = ~(_006_ ^ _013_);
endmodule

/// See issue #4832
//  !(d[32 + 3] & in[3]) & d[32 + 22]
//  was wrongly transformed to
//  !d[32 + 3] & d[32 + 22] & !in[3]
//  A subtree under NOT should be untouched, but was not.
//  Testing OR subtree too.
module bug4832(input wire clk, input wire [31:0] in, output out);
   logic [95:0] d;
   always_ff @(posedge clk)
      d <= {d[63:0], in};

   logic [31:0] tmp_and;
   logic [31:0] tmp_or;
   logic result_and;
   logic result_or;
   assign tmp_and = (d[63:32] & in) >> 3;
   assign tmp_or = (d[63:32] | in) >> 8;
   always_ff @(posedge clk) begin
      result_and <= !tmp_and[0] & d[32 + 22];
      result_or <= !tmp_or[0] | d[32 + 21];
   end
   assign out = result_and ^ result_or;
endmodule

/// See issue #4837 and $4841
// replaceShiftOp() in V3Const did not update widthMin, then bit-op-tree opt.
// was wrongly triggered for the subtree.
// replaceShiftOp() transforms as below:
//    SHIFT(AND(a,b),CONST)->AND(SHIFT(a,CONST),SHIFT(b,CONST))
// AND after the transformation must have same minWidth as the original SHIFT
// e.g. SHIFTL(AND(a, b), 1) => AND(SHIFTL(a, 1), SHIFTL(b, 1))
//      AND in the result must have 1 bit larger widthMin than the original AND
module bug4837(input wire clk, input wire [31:0] in, output out);
   logic [95:0] d;
   always_ff @(posedge clk)
      d <= {d[63:0], in};

   wire celloutsig_0z;
   wire [1:0] celloutsig_1z;
   wire celloutsig_2z;
   wire [95:0] out_data;
   assign celloutsig_0z = d[83] < d[74];
   assign celloutsig_1z = { d[54], celloutsig_0z } & { d[42], celloutsig_0z };
   assign celloutsig_2z = d[65:64] < d[83:82];
   assign { out_data[33:32], out_data[0] } = { celloutsig_1z, celloutsig_2z };

   assign out = out_data[33] ^ out_data[32] ^ out_data[0];
endmodule

// See issue #4857
// (1'b0 != (!a)) | b was wrongly optimized to
// (a | b) & 1'b1
// polarity was not considered when traversing NEQ under AND/OR tree
module bug4857(input wire clk, input wire [31:0] in, output out);
   logic [95:0] d;
   always_ff @(posedge clk)
      d <= {d[63:0], in};

   wire celloutsig_12z;
   wire celloutsig_15z;
   wire celloutsig_17z;
   wire celloutsig_4z;
   wire celloutsig_67z;
   wire celloutsig_9z;
   logic [95:0] in_data;
   logic result;

   // verilator lint_off UNDRIVEN
   wire [95:0] out_data;
   // verilator lint_on UNDRIVEN

   assign celloutsig_4z = ~(in_data[72] & in_data[43]);  // 1
   assign celloutsig_67z = | { in_data[64], celloutsig_12z }; // 0
   assign celloutsig_15z = in_data[43] & ~(celloutsig_4z); // 0
   assign celloutsig_9z = celloutsig_17z & ~(in_data[43]); // 00000000
   assign celloutsig_17z = celloutsig_15z & ~(in_data[43]);// 0
   assign celloutsig_12z = celloutsig_4z != celloutsig_9z; // 1
   assign out_data[32] = celloutsig_67z; // 1

   assign in_data = d;
   always_ff @ (posedge clk)
      result <= out_data[32];
   assign out = result;
endmodule


// See issue #4864
//  (((in_data[32*1] & 32'h3000000 != 0)        |  (in_data[32*2 + 25])| (sig_b != 9'b0)) >> 4) | sig_b[2]
// was wrongly optimized as below.
//   ((in_data[32]   & 32'h30000000) != 0 >> 0) |  (in_data[32*2 + 29])|((sig_b & 9'h1f4) != 0)
// The result of EQ/NE is just 1 bit width, so EQ/NE under SHFITR cannot be treated as a multi-bit term
// such as AND/OR.
module bug4864(input wire clk, input wire [31:0] in, output wire out);
   logic [159:0] clkin_data = '0;
   logic [95:0] in_data = '0;
   int cycle = 0;
   always @(posedge clk) begin
      if (in[0]) begin
         cycle <= cycle + 1;
         if (cycle == 0) begin
            clkin_data <= 160'hFFFFFFFF_00000000_00000000_00000000_00000000;
         end else if (cycle == 1) begin
            in_data <= 96'h00000000_FFFFFFFF_00000000;
         end else begin
            clkin_data <= 160'hFFFFFFFF_00000000_00000000_00000000_FFFFFFFF;
         end
      end
   end

   wire moveme;
   wire sig_a;
   reg [8:0] sig_b;
   wire sig_c;
   wire [20:0] sig_d;
   reg sig_e;

   logic myfirst, mysecond;
   assign myfirst  = 1'b0;
   assign mysecond = 1'b0;

   always_ff @(posedge clkin_data[0], posedge myfirst, posedge mysecond)
      if (myfirst) sig_e <= 1'b0;
      else if (mysecond) sig_e <= 1'b1;
      else if (clkin_data[128]) sig_e <= sig_d[7];

   always_ff @(posedge clkin_data[128])
      sig_b <= '0;

   assign sig_a = in_data[89]; // 1'b0;
   assign sig_c = | { in_data[61:60], sig_b, sig_a };
   assign sig_d = ~ { moveme, 6'b0, sig_b, 1'b0, sig_c, 3'b0 };
   assign moveme = 1'b1;

   assign out = sig_e;
endmodule
