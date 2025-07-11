// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t(/*AUTOARG*/
  // Inputs
  clk
  );
  input clk;

  int cyc;
  reg [63:0] crc;

  // Take CRC data and apply to testblock inputs
  wire a = crc[0];
  wire b = crc[1];

  /*AUTOWIRE*/

  Test test(.*);

  // Test loop
  always @(posedge clk) begin
`ifdef TEST_VERBOSE
    $write("[%0t] cyc==%0d crc=%x result=%x\n", $time, cyc, crc);
`endif
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    if (cyc == 0) begin
      // Setup
      crc <= 64'h5aef0c8d_d70a4497;
    end
    else if (cyc == 99) begin
      `checkh(crc, 64'hc77bb9b3784ea091);

      // Result check
      `checkd(test.count_hits_iff, 48);
      `checkd(test.count_hits_implies, 24);
      `checkd(test.count_hits_not, 47);

      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule

module Test(input clk,
            input int cyc,
            input a,
            input b);

  int count_hits_iff;
  int count_hits_implies;
  int count_hits_not;

  default disable iff cyc < 5;

  //        property_expr1 iff property_expr2: true if (!property_expr1 && !property_expr2) || (property_expr1 && property_expr2)
  assert property ( @(negedge clk) a iff b )
    else count_hits_iff = count_hits_iff + 1;

  //        property_expr1 implies property_expr2: true if !property_expr1 || property_expr2
  assert property ( @(negedge clk) a implies b )
    else count_hits_implies = count_hits_implies + 1;

  assert property ( @(negedge clk) not a )
    else count_hits_not = count_hits_not + 1;

endmodule
