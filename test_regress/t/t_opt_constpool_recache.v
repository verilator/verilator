// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t;
  logic clk = 1'b0;
  always #5 clk = ~clk;

  logic [31:0] cyc = 0;
  logic [3:0] idx;
  assign idx = cyc[3:0];

  // V3Case lowers this to a 512-bit constant-pool lookup table before V3Dead
  // calls AstConstPool::rebuildVarScopesAndCache().
  logic [31:0] case_word;
  always_comb
    case (idx)
      4'h0: case_word = 32'h00000000;
      4'h1: case_word = 32'h00000001;
      4'h2: case_word = 32'h00000002;
      4'h3: case_word = 32'h00000003;
      4'h4: case_word = 32'h00000004;
      4'h5: case_word = 32'h00000005;
      4'h6: case_word = 32'h00000006;
      4'h7: case_word = 32'h00000007;
      4'h8: case_word = 32'h00000008;
      4'h9: case_word = 32'h00000009;
      4'ha: case_word = 32'h0000000a;
      4'hb: case_word = 32'h0000000b;
      4'hc: case_word = 32'h0000000c;
      4'hd: case_word = 32'h0000000d;
      4'he: case_word = 32'h0000000e;
      default: case_word = 32'h0000000f;
    endcase

  localparam logic [511:0] TABLE = {
    32'h0000000f,
    32'h0000000e,
    32'h0000000d,
    32'h0000000c,
    32'h0000000b,
    32'h0000000a,
    32'h00000009,
    32'h00000008,
    32'h00000007,
    32'h00000006,
    32'h00000005,
    32'h00000004,
    32'h00000003,
    32'h00000002,
    32'h00000001,
    32'h00000000
  };

  // V3Premit extracts this matching wide constant after V3Dead recached the
  // const-pool contents created by V3Case.
  logic [31:0] static_word;
  assign static_word = TABLE[{idx, 5'b0}+:32];

  always @(posedge clk) begin
    `checkh(case_word, static_word);
    cyc <= cyc + 32'd1;
    if (cyc == 32'd32) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
