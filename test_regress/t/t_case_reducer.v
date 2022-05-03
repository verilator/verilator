// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2012 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer      cyc = 0;
   reg [63:0]   crc;
   reg [63:0]   sum;

   // Take CRC data and apply to testblock inputs
   wire [7:0]  operand_a = crc[7:0];
   wire [7:0]  operand_b = crc[15:8];

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [6:0]           out;                    // From test of Test.v
   // End of automatics

   Test test (/*AUTOINST*/
              // Outputs
              .out                      (out[6:0]),
              // Inputs
              .clk                      (clk),
              .operand_a                (operand_a[7:0]),
              .operand_b                (operand_b[7:0]));

   // Aggregate outputs into a single result vector
   wire [63:0] result = {57'h0, out};

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d crc=%x result=%x\n", $time, cyc, crc, result);
`endif
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
      sum <= result ^ {sum[62:0], sum[63] ^ sum[2] ^ sum[0]};
      if (cyc==0) begin
         // Setup
         crc <= 64'h5aef0c8d_d70a4497;
         sum <= 64'h0;
      end
      else if (cyc<10) begin
         sum <= 64'h0;
      end
      else if (cyc<90) begin
      end
      else if (cyc==99) begin
         $write("[%0t] cyc==%0d crc=%x sum=%x\n", $time, cyc, crc, sum);
         if (crc !== 64'hc77bb9b3784ea091) $stop;
         // What checksum will we end up with (above print should match)
`define EXPECTED_SUM 64'h8a78c2ec4946ac38
         if (sum !== `EXPECTED_SUM) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule

module Test
  (
   // Inputs
   input wire        clk,
   input wire [7:0]  operand_a, // operand a
   input wire [7:0]  operand_b, // operand b
             // Outputs
   output wire [6:0] out
   );

   wire [6:0]        clz_a;
   wire [6:0]        clz_b;

   clz u_clz_a
     (
      // Inputs
      .data_i      (operand_a),
      .out      (clz_a));

  clz u_clz_b
    (
     // Inputs
     .data_i      (operand_b),
     .out      (clz_b));

   assign out     = clz_a - clz_b;
`ifdef TEST_VERBOSE
   always @(posedge clk)
     $display("Out(%x) =  clz_a(%x) - clz_b(%x)", out, clz_a, clz_b);
`endif

endmodule

`define def_0000_001x 8'b0000_0010, 8'b0000_0011

`define def_0000_01xx 8'b0000_0100, 8'b0000_0101, 8'b0000_0110, 8'b0000_0111

`define def_0000_10xx 8'b0000_1000, 8'b0000_1001, 8'b0000_1010, 8'b0000_1011
`define def_0000_11xx 8'b0000_1100, 8'b0000_1101, 8'b0000_1110, 8'b0000_1111
`define def_0000_1xxx `def_0000_10xx, `def_0000_11xx

`define def_0001_00xx 8'b0001_0000, 8'b0001_0001, 8'b0001_0010, 8'b0001_0011
`define def_0001_01xx 8'b0001_0100, 8'b0001_0101, 8'b0001_0110, 8'b0001_0111
`define def_0001_10xx 8'b0001_1000, 8'b0001_1001, 8'b0001_1010, 8'b0001_1011
`define def_0001_11xx 8'b0001_1100, 8'b0001_1101, 8'b0001_1110, 8'b0001_1111

`define def_0010_00xx 8'b0010_0000, 8'b0010_0001, 8'b0010_0010, 8'b0010_0011
`define def_0010_01xx 8'b0010_0100, 8'b0010_0101, 8'b0010_0110, 8'b0010_0111
`define def_0010_10xx 8'b0010_1000, 8'b0010_1001, 8'b0010_1010, 8'b0010_1011
`define def_0010_11xx 8'b0010_1100, 8'b0010_1101, 8'b0010_1110, 8'b0010_1111

`define def_0011_00xx 8'b0011_0000, 8'b0011_0001, 8'b0011_0010, 8'b0011_0011
`define def_0011_01xx 8'b0011_0100, 8'b0011_0101, 8'b0011_0110, 8'b0011_0111
`define def_0011_10xx 8'b0011_1000, 8'b0011_1001, 8'b0011_1010, 8'b0011_1011
`define def_0011_11xx 8'b0011_1100, 8'b0011_1101, 8'b0011_1110, 8'b0011_1111

`define def_0100_00xx 8'b0100_0000, 8'b0100_0001, 8'b0100_0010, 8'b0100_0011
`define def_0100_01xx 8'b0100_0100, 8'b0100_0101, 8'b0100_0110, 8'b0100_0111
`define def_0100_10xx 8'b0100_1000, 8'b0100_1001, 8'b0100_1010, 8'b0100_1011
`define def_0100_11xx 8'b0100_1100, 8'b0100_1101, 8'b0100_1110, 8'b0100_1111

`define def_0101_00xx 8'b0101_0000, 8'b0101_0001, 8'b0101_0010, 8'b0101_0011
`define def_0101_01xx 8'b0101_0100, 8'b0101_0101, 8'b0101_0110, 8'b0101_0111
`define def_0101_10xx 8'b0101_1000, 8'b0101_1001, 8'b0101_1010, 8'b0101_1011
`define def_0101_11xx 8'b0101_1100, 8'b0101_1101, 8'b0101_1110, 8'b0101_1111

`define def_0110_00xx 8'b0110_0000, 8'b0110_0001, 8'b0110_0010, 8'b0110_0011
`define def_0110_01xx 8'b0110_0100, 8'b0110_0101, 8'b0110_0110, 8'b0110_0111
`define def_0110_10xx 8'b0110_1000, 8'b0110_1001, 8'b0110_1010, 8'b0110_1011
`define def_0110_11xx 8'b0110_1100, 8'b0110_1101, 8'b0110_1110, 8'b0110_1111

`define def_0111_00xx 8'b0111_0000, 8'b0111_0001, 8'b0111_0010, 8'b0111_0011
`define def_0111_01xx 8'b0111_0100, 8'b0111_0101, 8'b0111_0110, 8'b0111_0111
`define def_0111_10xx 8'b0111_1000, 8'b0111_1001, 8'b0111_1010, 8'b0111_1011
`define def_0111_11xx 8'b0111_1100, 8'b0111_1101, 8'b0111_1110, 8'b0111_1111

`define def_1000_00xx 8'b1000_0000, 8'b1000_0001, 8'b1000_0010, 8'b1000_0011
`define def_1000_01xx 8'b1000_0100, 8'b1000_0101, 8'b1000_0110, 8'b1000_0111
`define def_1000_10xx 8'b1000_1000, 8'b1000_1001, 8'b1000_1010, 8'b1000_1011
`define def_1000_11xx 8'b1000_1100, 8'b1000_1101, 8'b1000_1110, 8'b1000_1111

`define def_1001_00xx 8'b1001_0000, 8'b1001_0001, 8'b1001_0010, 8'b1001_0011
`define def_1001_01xx 8'b1001_0100, 8'b1001_0101, 8'b1001_0110, 8'b1001_0111
`define def_1001_10xx 8'b1001_1000, 8'b1001_1001, 8'b1001_1010, 8'b1001_1011
`define def_1001_11xx 8'b1001_1100, 8'b1001_1101, 8'b1001_1110, 8'b1001_1111

`define def_1010_00xx 8'b1010_0000, 8'b1010_0001, 8'b1010_0010, 8'b1010_0011
`define def_1010_01xx 8'b1010_0100, 8'b1010_0101, 8'b1010_0110, 8'b1010_0111
`define def_1010_10xx 8'b1010_1000, 8'b1010_1001, 8'b1010_1010, 8'b1010_1011
`define def_1010_11xx 8'b1010_1100, 8'b1010_1101, 8'b1010_1110, 8'b1010_1111

`define def_1011_00xx 8'b1011_0000, 8'b1011_0001, 8'b1011_0010, 8'b1011_0011
`define def_1011_01xx 8'b1011_0100, 8'b1011_0101, 8'b1011_0110, 8'b1011_0111
`define def_1011_10xx 8'b1011_1000, 8'b1011_1001, 8'b1011_1010, 8'b1011_1011
`define def_1011_11xx 8'b1011_1100, 8'b1011_1101, 8'b1011_1110, 8'b1011_1111

`define def_1100_00xx 8'b1100_0000, 8'b1100_0001, 8'b1100_0010, 8'b1100_0011
`define def_1100_01xx 8'b1100_0100, 8'b1100_0101, 8'b1100_0110, 8'b1100_0111
`define def_1100_10xx 8'b1100_1000, 8'b1100_1001, 8'b1100_1010, 8'b1100_1011
`define def_1100_11xx 8'b1100_1100, 8'b1100_1101, 8'b1100_1110, 8'b1100_1111

`define def_1101_00xx 8'b1101_0000, 8'b1101_0001, 8'b1101_0010, 8'b1101_0011
`define def_1101_01xx 8'b1101_0100, 8'b1101_0101, 8'b1101_0110, 8'b1101_0111
`define def_1101_10xx 8'b1101_1000, 8'b1101_1001, 8'b1101_1010, 8'b1101_1011
`define def_1101_11xx 8'b1101_1100, 8'b1101_1101, 8'b1101_1110, 8'b1101_1111

`define def_1110_00xx 8'b1110_0000, 8'b1110_0001, 8'b1110_0010, 8'b1110_0011
`define def_1110_01xx 8'b1110_0100, 8'b1110_0101, 8'b1110_0110, 8'b1110_0111
`define def_1110_10xx 8'b1110_1000, 8'b1110_1001, 8'b1110_1010, 8'b1110_1011
`define def_1110_11xx 8'b1110_1100, 8'b1110_1101, 8'b1110_1110, 8'b1110_1111

`define def_1111_00xx 8'b1111_0000, 8'b1111_0001, 8'b1111_0010, 8'b1111_0011
`define def_1111_01xx 8'b1111_0100, 8'b1111_0101, 8'b1111_0110, 8'b1111_0111
`define def_1111_10xx 8'b1111_1000, 8'b1111_1001, 8'b1111_1010, 8'b1111_1011
`define def_1111_11xx 8'b1111_1100, 8'b1111_1101, 8'b1111_1110, 8'b1111_1111

`define def_0001_xxxx `def_0001_00xx, `def_0001_01xx, `def_0001_10xx, `def_0001_11xx
`define def_0010_xxxx `def_0010_00xx, `def_0010_01xx, `def_0010_10xx, `def_0010_11xx
`define def_0011_xxxx `def_0011_00xx, `def_0011_01xx, `def_0011_10xx, `def_0011_11xx
`define def_0100_xxxx `def_0100_00xx, `def_0100_01xx, `def_0100_10xx, `def_0100_11xx
`define def_0101_xxxx `def_0101_00xx, `def_0101_01xx, `def_0101_10xx, `def_0101_11xx
`define def_0110_xxxx `def_0110_00xx, `def_0110_01xx, `def_0110_10xx, `def_0110_11xx
`define def_0111_xxxx `def_0111_00xx, `def_0111_01xx, `def_0111_10xx, `def_0111_11xx

`define def_1000_xxxx `def_1000_00xx, `def_1000_01xx, `def_1000_10xx, `def_1000_11xx
`define def_1001_xxxx `def_1001_00xx, `def_1001_01xx, `def_1001_10xx, `def_1001_11xx
`define def_1010_xxxx `def_1010_00xx, `def_1010_01xx, `def_1010_10xx, `def_1010_11xx
`define def_1011_xxxx `def_1011_00xx, `def_1011_01xx, `def_1011_10xx, `def_1011_11xx
`define def_1100_xxxx `def_1100_00xx, `def_1100_01xx, `def_1100_10xx, `def_1100_11xx
`define def_1101_xxxx `def_1101_00xx, `def_1101_01xx, `def_1101_10xx, `def_1101_11xx
`define def_1110_xxxx `def_1110_00xx, `def_1110_01xx, `def_1110_10xx, `def_1110_11xx
`define def_1111_xxxx `def_1111_00xx, `def_1111_01xx, `def_1111_10xx, `def_1111_11xx

`define def_1xxx_xxxx `def_1000_xxxx, `def_1001_xxxx, `def_1010_xxxx, `def_1011_xxxx, \
                      `def_1100_xxxx, `def_1101_xxxx, `def_1110_xxxx, `def_1111_xxxx
`define def_01xx_xxxx `def_0100_xxxx, `def_0101_xxxx, `def_0110_xxxx, `def_0111_xxxx
`define def_001x_xxxx `def_0010_xxxx, `def_0011_xxxx



module clz(
  input wire [7:0] data_i,
  output wire [6:0] out
);

  // -----------------------------
  // Reg declarations
  // -----------------------------

  reg [2:0]  clz_byte0;
  reg [2:0]  clz_byte1;
  reg [2:0]  clz_byte2;
  reg [2:0]  clz_byte3;

  always @*
    case (data_i)
      `def_1xxx_xxxx : clz_byte0 = 3'b000;
      `def_01xx_xxxx : clz_byte0 = 3'b001;
      `def_001x_xxxx : clz_byte0 = 3'b010;
      `def_0001_xxxx : clz_byte0 = 3'b011;
      `def_0000_1xxx : clz_byte0 = 3'b100;
      `def_0000_01xx : clz_byte0 = 3'b101;
      `def_0000_001x : clz_byte0 = 3'b110;
      8'b0000_0001   : clz_byte0 = 3'b111;
      8'b0000_0000   : clz_byte0 = 3'b111;
      default        : clz_byte0 = 3'bxxx;
    endcase

  always @*
    case (data_i)
      `def_1xxx_xxxx : clz_byte1 = 3'b000;
      `def_01xx_xxxx : clz_byte1 = 3'b001;
      `def_001x_xxxx : clz_byte1 = 3'b010;
      `def_0001_xxxx : clz_byte1 = 3'b011;
      `def_0000_1xxx : clz_byte1 = 3'b100;
      `def_0000_01xx : clz_byte1 = 3'b101;
      `def_0000_001x : clz_byte1 = 3'b110;
      8'b0000_0001   : clz_byte1 = 3'b111;
      8'b0000_0000   : clz_byte1 = 3'b111;
      default        : clz_byte1 = 3'bxxx;
    endcase

  always @*
    case (data_i)
      `def_1xxx_xxxx : clz_byte2 = 3'b000;
      `def_01xx_xxxx : clz_byte2 = 3'b001;
      `def_001x_xxxx : clz_byte2 = 3'b010;
      `def_0001_xxxx : clz_byte2 = 3'b011;
      `def_0000_1xxx : clz_byte2 = 3'b100;
      `def_0000_01xx : clz_byte2 = 3'b101;
      `def_0000_001x : clz_byte2 = 3'b110;
      8'b0000_0001   : clz_byte2 = 3'b111;
      8'b0000_0000   : clz_byte2 = 3'b111;
      default        : clz_byte2 = 3'bxxx;
    endcase
  always @*
    case (data_i)
      `def_1xxx_xxxx : clz_byte3 = 3'b000;
      `def_01xx_xxxx : clz_byte3 = 3'b001;
      `def_001x_xxxx : clz_byte3 = 3'b010;
      `def_0001_xxxx : clz_byte3 = 3'b011;
      `def_0000_1xxx : clz_byte3 = 3'b100;
      `def_0000_01xx : clz_byte3 = 3'b101;
      `def_0000_001x : clz_byte3 = 3'b110;
      8'b0000_0001   : clz_byte3 = 3'b111;
      8'b0000_0000   : clz_byte3 = 3'b111;
      default        : clz_byte3 = 3'bxxx;
    endcase

  assign out = {4'b0000, clz_byte1};

endmodule // clz
