// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Ethan Sifferman
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Test that mixing whole-variable and partial NBAs with suspend points
// correctly implements "last NBA wins" semantics for both scalars and arrays.

module t;

  int delay = 0;
  always #1 delay = int'($time) / 4;
  task automatic do_delay;
    // verilator lint_off ZERODLY
    if (delay > 0) #(delay);
    // verilator lint_on ZERODLY
  endtask

  // ---- Scalar tests ----

  // Test S1: whole then partial with suspend between
  logic [7:0] s1 = 0;
  always begin
    s1 <= 8'hff;
    do_delay();
    s1[3:0] <= 4'h0;
    #1;
    `checkh(s1, 8'hf0)
  end

  // Test S2: partial then whole with suspend between
  logic [7:0] s2 = 0;
  always begin
    s2[3:0] <= 4'h0;
    do_delay();
    s2 <= 8'hff;
    #1;
    `checkh(s2, 8'hff)
  end

  // Test S3: two partials to non-overlapping ranges
  logic [7:0] s3 = 0;
  always begin
    s3[7:4] <= 4'ha;
    do_delay();
    s3[3:0] <= 4'h5;
    #1;
    `checkh(s3, 8'ha5)
  end

  // Test S4: two partials to same range (last wins)
  logic [7:0] s4 = 0;
  always begin
    s4[3:0] <= 4'ha;
    do_delay();
    s4[3:0] <= 4'h5;
    #1;
    `checkh(s4, 8'h05)
  end

  // Test S5: whole, partial, whole (last wins)
  logic [7:0] s5 = 0;
  always begin
    s5 <= 8'haa;
    do_delay();
    s5[3:0] <= 4'hb;
    do_delay();
    s5 <= 8'hcc;
    #1;
    `checkh(s5, 8'hcc)
  end

  // ---- Unpacked array element tests ----

  // Checked by an index not known statically, so the arrays are not split into variables
  int k;
  initial k = $urandom_range(0, 0);

  // Test A1: whole element then partial element with suspend between
  logic [7:0] a1[0:3];
  initial for (int i = 0; i < 4; i++) a1[i] = 0;
  always begin
    a1[1] <= 8'hff;
    do_delay();
    a1[1][3:0] <= 4'h0;
    #1;
    `checkh(a1[k+1], 8'hf0)
  end

  // Test A2: partial element then whole element with suspend between
  logic [7:0] a2[0:3];
  initial for (int i = 0; i < 4; i++) a2[i] = 0;
  always begin
    a2[2][7:4] <= 4'hf;
    do_delay();
    a2[2] <= 8'h00;
    #1;
    `checkh(a2[k+2], 8'h00)
  end

  // Test A3: writes to different indices (both should apply)
  logic [7:0] a3[0:3];
  initial for (int i = 0; i < 4; i++) a3[i] = 0;
  always begin
    a3[0] <= 8'haa;
    do_delay();
    a3[1] <= 8'hbb;
    #1;
    `checkh(a3[k], 8'haa)
    `checkh(a3[k+1], 8'hbb)
  end

  // Test A4: same index overwrite (last wins)
  logic [7:0] a4[0:3];
  initial for (int i = 0; i < 4; i++) a4[i] = 0;
  always begin
    a4[0] <= 8'haa;
    do_delay();
    a4[0] <= 8'hbb;
    #1;
    `checkh(a4[k], 8'hbb)
  end

  // ---- Full array assignment tests ----

  // Test F1: full array then element (element write wins for that index)
  logic [7:0] f1[0:3];
  initial for (int i = 0; i < 4; i++) f1[i] = 0;
  logic [7:0] f1_src[0:3];
  initial begin
    f1_src[0] = 8'h11;
    f1_src[1] = 8'h22;
    f1_src[2] = 8'h33;
    f1_src[3] = 8'h44;
  end
  always begin
    f1 <= f1_src;
    do_delay();
    f1[1] <= 8'hff;
    #1;
    `checkh(f1[k], 8'h11)
    `checkh(f1[k+1], 8'hff)
    `checkh(f1[k+2], 8'h33)
    `checkh(f1[k+3], 8'h44)
  end

  // Test F2: element then full array (full array wins)
  logic [7:0] f2[0:3];
  initial for (int i = 0; i < 4; i++) f2[i] = 0;
  logic [7:0] f2_src[0:3];
  initial begin
    f2_src[0] = 8'h11;
    f2_src[1] = 8'h22;
    f2_src[2] = 8'h33;
    f2_src[3] = 8'h44;
  end
  always begin
    f2[1] <= 8'hff;
    do_delay();
    f2 <= f2_src;
    #1;
    `checkh(f2[k], 8'h11)
    `checkh(f2[k+1], 8'h22)
    `checkh(f2[k+2], 8'h33)
    `checkh(f2[k+3], 8'h44)
  end

  // Test F3: full array then partial element (partial wins for that element's bits)
  logic [7:0] f3[0:3];
  initial for (int i = 0; i < 4; i++) f3[i] = 0;
  logic [7:0] f3_src[0:3];
  initial begin
    f3_src[0] = 8'haa;
    f3_src[1] = 8'hbb;
    f3_src[2] = 8'hcc;
    f3_src[3] = 8'hdd;
  end
  always begin
    f3 <= f3_src;
    do_delay();
    f3[2][3:0] <= 4'h0;
    #1;
    `checkh(f3[k], 8'haa)
    `checkh(f3[k+1], 8'hbb)
    `checkh(f3[k+2], 8'hc0)
    `checkh(f3[k+3], 8'hdd)
  end

  // Test F4: partial element then full array (full array wins)
  logic [7:0] f4[0:3];
  initial for (int i = 0; i < 4; i++) f4[i] = 0;
  logic [7:0] f4_src[0:3];
  initial begin
    f4_src[0] = 8'haa;
    f4_src[1] = 8'hbb;
    f4_src[2] = 8'hcc;
    f4_src[3] = 8'hdd;
  end
  always begin
    f4[2][3:0] <= 4'hf;
    do_delay();
    f4 <= f4_src;
    #1;
    `checkh(f4[k], 8'haa)
    `checkh(f4[k+1], 8'hbb)
    `checkh(f4[k+2], 8'hcc)
    `checkh(f4[k+3], 8'hdd)
  end

  // ---- One NBA executed twice in a time step, to another part each time ----

  // Test R1: partial with a varying range (both should apply)
  logic [7:0] r1 = 0;
  bit r1_hi;
  always begin
    r1[r1_hi*4+:4] <= r1_hi ? 4'h5 : 4'ha;
    r1_hi = ~r1_hi;
    if (r1_hi) do_delay();
    else begin
      #1;
      `checkh(r1, 8'h5a)
    end
  end

  // Test R2: elements with a varying index, also of structs (both should apply)
  typedef struct {
    logic [7:0] f;
    logic [7:0] g;
  } pair_t;
  logic [7:0] r2[0:1];
  pair_t r2s[0:1];
  bit r2_i;
  always begin
    r2[r2_i] <= r2_i ? 8'h55 : 8'haa;
    r2s[r2_i] <= '{f: r2_i ? 8'h77 : 8'h88, g: 0};
    r2_i = ~r2_i;
    if (r2_i) do_delay();
    else begin
      #1;
      `checkh(r2[k], 8'haa)
      `checkh(r2[k+1], 8'h55)
      `checkh(r2s[k].f, 8'h88)
      `checkh(r2s[k+1].f, 8'h77)
    end
  end

  initial begin
    #20;
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
