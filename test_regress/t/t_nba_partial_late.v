// DESCRIPTION: Verilator: Constant partial nonblocking assignments
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%p exp=%p (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);
  int cyc = 0;
  always @(posedge clk) cyc <= cyc + 1;
  always @(negedge clk) begin
    if (cyc == 18) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  nba_partial #(
      .W(95),
      .BASE(6)
  ) narrow_low (
      .clk,
      .cyc
  );
  nba_partial #(
      .W(95)
  ) narrow_high (
      .clk,
      .cyc
  );
  nba_partial #(
      .W(4097)
  ) wide (
      .clk,
      .cyc
  );
  nba_partial #(
      .W(4099),
      .ASC(1)
  ) wide_other (
      .clk,
      .cyc
  );

  nba_fallback fallback (
      .clk,
      .cyc
  );
endmodule

module nba_fallback (
    input clk,
    input int cyc
);
  bit [4096:0] direct;
  bit [4096:0] direct_expected;
  bit [4096:0] mixed;
  bit [4096:0] mixed_expected;
  bit [4096:0] looped;
  bit [4096:0] looped_expected;
  bit [16:0][32:0] dense;
  bit [16:0][32:0] dense_expected;
  bit [94:0] ends = '1;
  bit [94:0] ends_expected = '1;
  bit [94:0] overrun = '1;
  bit [94:0] overrun_expected = '1;

  always @(posedge clk) begin
    `checkh(direct, direct_expected);
    direct_expected[cyc%4097] = cyc[0];
    direct[cyc%4097] <= cyc[0];

    `checkh(mixed, mixed_expected);
    mixed_expected = mixed;
    if (cyc[0]) begin
      mixed <= '0;
      mixed_expected = '0;
    end
    mixed[cyc%4097] <= mixed[(cyc+1)%4097] ^ cyc[1];
    mixed_expected[cyc%4097] = mixed[(cyc+1)%4097] ^ cyc[1];

    `checkh(looped, looped_expected);
    looped_expected = looped;
    // Each assignment can execute more than once per clock cycle.
    for (int i = 0; i < (cyc & 3) + 1; ++i) begin
      looped[cyc+i] <= looped[cyc+i+1] ^ cyc[0];
      looped_expected[cyc+i] = looped[cyc+i+1] ^ cyc[0];
    end

    `checkh(dense, dense_expected);
    dense_expected = {dense[15:0], 1'b0, 32'(cyc + 1)};
    // Individually partial writes collectively update the entire pipeline.
    for (int i = 16; i > 0; --i) dense[i] <= dense[i-1];
    dense[0] <= {1'b0, 32'(cyc + 1)};

    `checkh(ends, ends_expected);
    ends_expected[0] = cyc[0];
    ends_expected[94] = ends[0];
    ends[0] <= cyc[0];
    ends[94] <= ends[0];

    // Only the in-range bits of this partly out-of-range slice are written.
    `checkh(overrun, overrun_expected);
    overrun_expected[94:91] = cyc[3:0];
    overrun_expected[0] = overrun[91];
    overrun[91+:7] <= cyc[6:0];
    overrun[0] <= overrun[91];
  end
endmodule

module nba_partial #(
    parameter W = 4097,
    parameter ASC = 0,
    parameter BASE = 65
) (
    input clk,
    input int cyc
);
  typedef bit [(ASC ? 3 : W+2):(ASC ? W+2 : 3)] state_t;
  state_t q = '1;
  state_t expected = '1;
  bit [32:0] value;

  always @(posedge clk) begin
    `checkh(q, expected);
    expected = q;
    value = {cyc[0], 32'(cyc * 76543)};
    if (cyc[0]) begin
      q[BASE+:33] <= value;
      expected[BASE+:33] = value;
    end
    if (cyc[1]) begin
      // Overlapping writes use old values, keep their order, and preserve untouched bits.
      q[BASE+7+:9] <= q[BASE+:9] ^ value[8:0];
      expected[BASE+7+:9] = q[BASE+:9] ^ value[8:0];
    end
    if (cyc[2]) begin
      q[BASE-3] <= 1'b1;
      expected[BASE-3] = 1'b1;
    end
    // Repeated updates to the same bit.
    for (int i = 0; i < (cyc & 3); ++i) begin
      q[BASE+2] <= q[BASE+3] ^ 1'(cyc >> i);
      expected[BASE+2] = q[BASE+3] ^ 1'(cyc >> i);
    end
  end
endmodule
