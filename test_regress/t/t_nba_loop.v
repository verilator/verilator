// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);
  int cyc = 0;
  int n = 3;
  always_ff @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 1) n <= 2;
  end
  always @(posedge clk) begin
    if (cyc == 4) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  // Shift register written as a loop of non-blocking bit assignments.
  logic [2:0] q = 3'b111;
  always_ff @(posedge clk) for (int i = 0; i < 3; ++i) q[i] <= (i > 0) ? q[i-1] : 1'b0;
  always @(posedge clk) begin
    if (cyc == 1) `checkh(q, 3'b110);
    if (cyc == 2) `checkh(q, 3'b100);
    if (cyc == 3) `checkh(q, 3'b000);
  end

  // Wide shift register exceeding default --unroll-count.
  logic [69:0] wide_q = 70'h3fff_ffff_ffff_ffff_ff;
  always_ff @(posedge clk) for (int i = 0; i < 70; ++i) wide_q[i] <= (i > 0) ? wide_q[i-1] : 1'b0;
  always @(posedge clk) begin
    if (cyc == 1) `checkh(wide_q, 70'h3fff_ffff_ffff_ffff_fe);
    if (cyc == 2) `checkh(wide_q, 70'h3fff_ffff_ffff_ffff_fc);
    if (cyc == 3) `checkh(wide_q, 70'h3fff_ffff_ffff_ffff_f8);
  end

  // Whole-vector NBA inside a dynamically bounded loop.
  logic [7:0] whole_q = 8'd10;
  always_ff @(posedge clk) for (int i = 0; i < n; ++i) whole_q <= whole_q + 8'd1;
  always @(posedge clk) begin
    if (cyc == 1) `checkd(whole_q, 11);
    if (cyc == 2) `checkd(whole_q, 12);
    if (cyc == 3) `checkd(whole_q, 13);
  end

  // Separate read statement before write statement in the same loop.
  logic [2:0] sep_q = 3'b101;
  logic [2:0] sep_cap = 3'b000;
  always_ff @(posedge clk) begin
    for (int i = 0; i < 3; ++i) begin
      sep_cap[i] <= sep_q[0];
      sep_q[0] <= 1'b0;
    end
  end
  always @(posedge clk) begin
    if (cyc == 1) begin
      `checkh(sep_cap, 3'b111);
      `checkh(sep_q, 3'b100);
    end
    if (cyc == 2) begin
      `checkh(sep_cap, 3'b000);
      `checkh(sep_q, 3'b100);
    end
  end

  // Read in loop condition, write in loop body.
  logic [2:0] cond_q = 3'b001;
  int cond_steps = 0;
  always_ff @(posedge clk) begin
    int k;
    k = 0;
    while (cond_q[0] && k < 3) begin
      cond_q[0] <= 1'b0;
      k = k + 1;
    end
    cond_steps <= k;
  end
  always @(posedge clk) begin
    if (cyc == 1) begin
      `checkd(cond_steps, 3);
      `checkh(cond_q, 3'b000);
    end
    if (cyc == 2) begin
      `checkd(cond_steps, 0);
      `checkh(cond_q, 3'b000);
    end
  end

  // Read in then-branch, write in else-branch inside a loop.
  logic [2:0] br_q = 3'b111;
  logic [2:0] br_out = 3'b000;
  always_ff @(posedge clk) begin
    for (int i = 0; i < 2; ++i) begin
      if (i == 1) br_out <= br_q;
      else br_q[0] <= 1'b0;
    end
  end
  always @(posedge clk) begin
    if (cyc == 1) begin
      `checkh(br_out, 3'b111);
      `checkh(br_q, 3'b110);
    end
    if (cyc == 2) begin
      `checkh(br_out, 3'b110);
      `checkh(br_q, 3'b110);
    end
  end

  // Nested loops: outer reads, inner writes.
  logic [2:0] nq1 = 3'b111;
  logic [1:0] nout1 = 2'b00;
  always_ff @(posedge clk) begin
    for (int i = 0; i < 2; ++i) begin
      nout1[i] <= nq1[0];
      for (int j = 0; j < 2; ++j) nq1[j] <= 1'b0;
    end
  end
  always @(posedge clk) begin
    if (cyc == 1) begin
      `checkh(nout1, 2'b11);
      `checkh(nq1, 3'b100);
    end
    if (cyc == 2) begin
      `checkh(nout1, 2'b00);
      `checkh(nq1, 3'b100);
    end
  end

  // Nested loops: inner loop 1 reads, inner loop 2 writes under common outer loop.
  logic [2:0] nq2 = 3'b111;
  logic [2:0] nout2 = 3'b000;
  always_ff @(posedge clk) begin
    for (int i = 0; i < 2; ++i) begin
      for (int j = 0; j < 3; ++j) nout2[j] <= nq2[j];
      for (int j = 0; j < 3; ++j) nq2[j] <= 1'b0;
    end
  end
  always @(posedge clk) begin
    if (cyc == 1) begin
      `checkh(nout2, 3'b111);
      `checkh(nq2, 3'b000);
    end
    if (cyc == 2) begin
      `checkh(nout2, 3'b000);
      `checkh(nq2, 3'b000);
    end
  end

  // Non-inlined function passed target by value inside a loop writing target.
  logic [2:0] fn_q = 3'b111;
  function automatic logic read_fn_q(input logic [2:0] v, input int idx);
    // verilator no_inline_task
    return v[idx];
  endfunction
  always_ff @(posedge clk) begin
    for (int i = 0; i < 3; ++i) fn_q[i] <= (i > 0) ? read_fn_q(fn_q, i - 1) : 1'b0;
  end
  always @(posedge clk) begin
    if (cyc == 1) `checkh(fn_q, 3'b110);
    if (cyc == 2) `checkh(fn_q, 3'b100);
    if (cyc == 3) `checkh(fn_q, 3'b000);
  end

  // Write-only loop (no read of target inside loop).
  logic [2:0] safe_wr = 3'b000;
  always_ff @(posedge clk) for (int i = 0; i < 3; ++i) safe_wr[i] <= cyc[0];
  always @(posedge clk) begin
    if (cyc == 1) `checkh(safe_wr, 3'b000);
    if (cyc == 2) `checkh(safe_wr, 3'b111);
    if (cyc == 3) `checkh(safe_wr, 3'b000);
  end

  // Disjoint sequential loops: first loop reads target, second loop writes target.
  logic [2:0] safe_seq = 3'b101;
  logic [2:0] safe_out = 3'b000;
  always_ff @(posedge clk) begin
    for (int i = 0; i < 3; ++i) safe_out[i] <= safe_seq[i];
    for (int i = 0; i < 3; ++i) safe_seq[i] <= cyc[0];
  end
  always @(posedge clk) begin
    if (cyc == 1) begin
      `checkh(safe_out, 3'b101);
      `checkh(safe_seq, 3'b000);
    end
    if (cyc == 2) begin
      `checkh(safe_out, 3'b000);
      `checkh(safe_seq, 3'b111);
    end
    if (cyc == 3) begin
      `checkh(safe_out, 3'b111);
      `checkh(safe_seq, 3'b000);
    end
  end

  // Wide partial constant-offset write inside a loop.
  logic [94:0] wide_p = {63'h5555_5555_5555_5555, 32'h0000_0001};
  always_ff @(posedge clk) for (int i = 0; i < 3; ++i) wide_p[7:0] <= wide_p[7:0] + 8'd1;
  always @(posedge clk) begin
    if (cyc == 1) `checkh(wide_p, {63'h5555_5555_5555_5555, 32'h0000_0002});
    if (cyc == 2) `checkh(wide_p, {63'h5555_5555_5555_5555, 32'h0000_0003});
    if (cyc == 3) `checkh(wide_p, {63'h5555_5555_5555_5555, 32'h0000_0004});
  end
endmodule
