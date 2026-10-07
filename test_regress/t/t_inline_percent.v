// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module leaf (
    input logic clk,
    input logic [31:0] data,
    output logic [31:0] result
);
  logic [31:0] words[31];
  for (genvar i = 0; i < 31; i++) begin : g
    always_ff @(posedge clk) words[i] <= data + 32'(i);
  end
  always_comb begin
    result = '0;
    foreach (words[i]) result ^= words[i];
  end
endmodule

module pair (
    input logic clk,
    input logic [31:0] data,
    output logic [31:0] result
);
  logic [31:0] a;
  logic [31:0] b;
  leaf u_a (.clk, .data, .result(a));
  leaf u_b (.clk, .data(data + 43), .result(b));
  assign result = a ^ b;
endmodule

module t (
    input logic clk
);
  int unsigned cycles = 0;
  logic [31:0] a;
  logic [31:0] b;
  pair u_a (.clk, .data(cycles), .result(a));
  pair u_b (.clk, .data(cycles + 71), .result(b));

  // Keep the shared hierarchy below the default design-size percentage limits.
  logic [31:0] words[1023];
  logic [31:0] result;
  for (genvar i = 0; i < 1023; i++) begin : g
    always_ff @(posedge clk) words[i] <= cycles + 32'(i);
  end
  always_comb begin
    result = '0;
    foreach (words[i]) result ^= words[i];
  end

  function automatic logic [31:0] prefix_xor(input logic [31:0] value);
    case (value[1:0])
      0: return value;
      1: return 1;
      2: return value + 1;
      default: return 0;
    endcase
  endfunction

  function automatic logic [31:0] expected(input logic [31:0] value);
    return prefix_xor(value + 30) ^ prefix_xor(value - 1)
        ^ prefix_xor(value + 73) ^ prefix_xor(value + 42);
  endfunction

  always @(posedge clk) cycles <= cycles + 1;
  always @(negedge clk) begin
    if (cycles > 0) begin
      `checkh(a, expected(cycles - 1));
      `checkh(b, expected(cycles + 70));
      `checkh(result, prefix_xor(cycles + 1021) ^ prefix_xor(cycles - 2));
    end
    if (cycles == 40) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
