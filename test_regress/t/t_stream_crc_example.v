// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0
`define stop $stop
`define checkh(gotv,
               expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,
               expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

typedef bit bit_q_t[$];

module t (  /*AUTOARG*/
    // Inputs
    clk
);
  input clk;
  integer        cyc = 0;
  reg     [63:0] crc = '0;
  reg     [63:0] sum = '0;

  // Take CRC data and apply to testblock inputs
  wire    [31:0] in = crc[31:0];

  /*AUTOWIRE*/
  // Beginning of automatic wires (for undeclared instantiated-module outputs)
  wire    [31:0] out;  // From test of Test.v
  // End of automatics

  Test test (
      .clk,
      .in,
      .out
  );

  // Aggregate outputs into a single result vector
  wire [63:0] result = {32'h0, out};

  initial begin
    byte unsigned p[$];
    byte unsigned po[$];
    bit bits[$];
    string s;

    p = {8'h84, 8'haa};
    `checkh(p[0], 8'h84);
    `checkh(p[1], 8'haa);

    bits = {<<8{bit_q_t'({<<{p}})}};
    bits.push_front(1'b0);
    po = {<<8{bit_q_t'({<<{bits}})}};

    s  = $sformatf("p=%p", p);
    `checks(s, "p='{'h84, 'haa} ");

    s = $sformatf("bits=%p", bits);
    `checks(s,
            "bits='{'h0, 'h0, 'h0, 'h1, 'h0, 'h0, 'h0, 'h0, 'h1, 'h0, 'h1, 'h0, 'h1, 'h0, 'h1, 'h0, 'h1} ");

    s = $sformatf("po=%p", po);
    `checks(s, "po='{'h8, 'h55, 'h80} ");
  end

  always_ff @(posedge clk) begin
`ifdef TEST_VERBOSE
    $write("[%0t] cyc==%0d crc=%x result=%x sum=%x\n", $time, cyc, crc, result, sum);
`endif

    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    sum <= result ^ {sum[62:0], sum[63] ^ sum[2] ^ sum[0]};

    if (cyc == 0) begin
      crc <= 64'h5aef0c8d_d70a4497;
      sum <= '0;
    end else if (cyc < 10) begin
      sum <= '0;
    end else if (cyc == 99) begin
      `checkh(crc, 64'hc77bb9b3784ea091);
      `checkh(sum, 64'h9721d4e989defb24);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule

module Test (
    input logic clk,
    input logic [31:0] in,
    output logic [31:0] out
);
  byte unsigned p[$];
  byte unsigned po[$];
  bit bits[$];

  always_ff @(posedge clk) begin
    p = {in[31:24], in[23:16], in[15:8], in[7:0]};
    bits = {<<8{bit_q_t'({<<{p}})}};
    bits.push_front(1'b0);
    po = {<<8{bit_q_t'({<<{bits}})}};
    out <= {po[3], po[2], po[1], po[0]};
  end
endmodule
