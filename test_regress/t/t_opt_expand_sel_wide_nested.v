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

  //--------------------------------------------------------------------
  // Stimulus/test driver

  logic clk = 0;
  always #5 clk = ~clk;
  int cyc = 0;
  logic [31:0] rng = 32'h1234_5678;

  function automatic logic [31:0] xorshift(input logic [31:0] x);
    logic [31:0] r;
    r = x ^ (x << 13);
    r = r ^ (r >> 17);
    r = r ^ (r << 5);
    return r;
  endfunction

  always @(posedge clk) begin
    cyc <= cyc + 1;
    rng <= xorshift(rng);
    if (cyc == 500) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  //--------------------------------------------------------------------
  // Deeply nested variable offset selects from a wide value.

  logic [15:0][31:0] lut = '0;
  logic [31:0]       arr[16] = '{default: 32'h0}; // Same as 'lut', but unpacked
  logic [3:0]        start = 4'h0;

  // Explicitly nested so test doesn't depend on unrolling/dfg, or other opts
  wire [3:0] chainLut
      = 4'(lut[4'(lut[4'(lut[4'(lut[4'(lut[4'(lut[4'(lut[4'(lut[start])])])])])])])]);
  wire [3:0] chainArr
      = 4'(arr[4'(arr[4'(arr[4'(arr[4'(arr[4'(arr[4'(arr[4'(arr[start])])])])])])])]);

  // Check exponential expansion
  always @(posedge clk) begin
    `checkh(chainLut, chainArr);

    // Shift a new entry into 'lut' and into its reference array in step
    lut <= {lut[14:0], rng};
    for (int i = 15; i > 0; --i) arr[i] <= arr[i-1];
    arr[0] <= rng;
    start <= rng[3:0];
  end

  //--------------------------------------------------------------------
  // Check access boundaries

  logic [511:0] data = 512'h0;
  logic [8:0]   lsb = 9'h0;

  wire [0:0]  sel01 = data[lsb+:01];
  wire [3:0]  sel04 = data[lsb+:04];
  wire [30:0] sel31 = data[lsb+:31];
  wire [31:0] sel32 = data[lsb+:32];
  wire [32:0] sel33 = data[lsb+:33];
  wire [63:0] sel64 = data[lsb+:64];

  always @(posedge clk) begin
    `checkh(sel01,  1'(data >> lsb));
    `checkh(sel04,  4'(data >> lsb));
    `checkh(sel31, 31'(data >> lsb));
    `checkh(sel32, 32'(data >> lsb));
    `checkh(sel33, 33'(data >> lsb));
    `checkh(sel64, 64'(data >> lsb));

    // Sweep every offset, so all word alignments are covered. Stop at 448,
    // so that even the widest select stays in range and the reference is
    // defined.
    lsb <= 9'(cyc % 449);
    data <= {data[479:0], ~rng};
  end

endmodule
