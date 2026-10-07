// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t;
  bit clk1 = 1'b0;
  bit clk2 = 1'b0;
  always #5 clk1 = ~clk1;
  always #10 clk2 = ~clk2;

  int iarray[63:0];
  int oarray1[63:0];
  int oarray2[63:0];

  initial begin
    for (int i = 0; i < 64; i = i + 1) begin
      iarray[i] = i;
    end

    #100;

    for (int i = 0; i < 64; i = i + 1) begin
      $display("%d %d %d", i, oarray1[i], oarray2[i]);
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end

  always @(posedge clk1) begin
    for (int i = 0; i < 64; i = i + 1) begin
      oarray1[i] = iarray[i];
    end
  end
  always @(posedge clk2) begin
    for (int i = 0; i < 64; i = i + 1) begin
      oarray2[i] = iarray[i];
    end
  end

  // Negative and non-unit strides
  initial begin
    int src[15:0];
    logic [6:0] dst[7:0];
    int seed;
    seed = 1234;
    for (int i = 0; i < 16; i = i + 1) begin
      src[i] = seed + i;
    end
    for (int i = 0; i < 8; i = i + 1) begin
      dst[7 - i] = 7'(src[2 * i]) ^ 7'(5 * i);
    end
    for (int i = 0; i < 8; i = i + 1) begin
      `checkd(dst[7 - i], 7'(seed + 2 * i) ^ 7'(5 * i));
    end
  end

  // Signed narrow constants, which V3Const moves to the left of the comparisons. Only the
  // first three roll, as the 4-bit thresholds wrap from 4'hf to 4'h0, breaking the stride.
  initial begin
    logic signed [3:0] sx[3:0];
    int cnt;
    for (int i = 0; i < 4; i = i + 1) begin
      sx[i] = 4'sd1;
    end
    cnt = 0;
    if (sx[0] < -4'sd3) cnt = cnt + 1;
    if (sx[1] < -4'sd2) cnt = cnt + 1;
    if (sx[2] < -4'sd1) cnt = cnt + 1;
    if (sx[3] < 4'sd0) cnt = cnt + 1;
    `checkd(cnt, 0);
  end

  // Replication counts, which set the width and must stay constant
  initial begin
    int rep[1:0];
    logic b[0:0];
    b[0] = 1'b1;
    rep[0] = 32'({4{b[0]}});
    rep[1] = 32'({8{b[0]}});
    `checkd(rep[0], 32'hf);
    `checkd(rep[1], 32'hff);
  end

  // Inlined calls, leaving a comment between the statements of the run
  int farray[63:0];
  int fseed;
  function automatic void setf(int i);
    farray[i] = fseed + 3 * i;
  endfunction
  initial begin
    fseed = 4321;
    for (int i = 0; i < 64; i = i + 1) begin
      setf(i);
    end
    for (int i = 0; i < 64; i = i + 1) begin
      `checkd(farray[i], fseed + 3 * i);
    end
  end

  // Streaming operator, whose slice size must stay constant
  function automatic logic [6:0] rev2(logic [6:0] v);
    return {<<2{v}};
  endfunction
  initial begin
    logic [6:0] sin[7:0];
    logic [6:0] sout[7:0];
    int seed;
    seed = 77;
    for (int i = 0; i < 8; i = i + 1) begin
      sin[i] = 7'(seed + i);
    end
    for (int i = 0; i < 8; i = i + 1) begin
      sout[i] = {<<2{sin[i]}};
    end
    for (int i = 0; i < 8; i = i + 1) begin
      `checkd(sout[i], rev2(7'(seed + i)));
    end
  end

  // Statements with the same node types, but a different number of replaceable constants,
  // or more or fewer nodes
  initial begin
    int a[1:0];
    longint q[0:0];
    int b;
    longint r;
    b = 1000;
    r = 64'h1_2345_6789;
    a[0] = b + 1;
    a[1] = b + 2;
    q[0] = r + 3;
    `checkd(a[0], b + 1);
    `checkd(a[1], b + 2);
    `checkd(q[0], r + 3);
    $display("%0d %0d", a[0], a[1]);
    $display("%0d", a[0]);
    $display("%0d %0d", a[0], a[1]);
  end

  // Loops not unrolled, with a break and waiting inside them, then a fork
  initial begin
    int cnt;
    int lim;
    cnt = 0;
    lim = 3;
    forever begin
      @(posedge clk1);
      cnt = cnt + 1;
      if (cnt == lim) break;
    end
    `checkd(cnt, lim);
    fork
      @(posedge clk1) cnt = cnt + 1;
      @(posedge clk2) cnt = cnt + 1;
    join
    `checkd(cnt, lim + 2);
  end

endmodule
