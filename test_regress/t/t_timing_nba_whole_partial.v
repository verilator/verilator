// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Ethan Sifferman
// SPDX-License-Identifier: CC0-1.0

// Test that mixing whole-variable and partial NBAs with suspend points
// correctly implements "last NBA wins" semantics for both scalars and arrays.

module t;

  int delay = 0; always #1 delay = int'($time) / 4;
  task automatic do_delay;
    if (delay > 0) #(delay);
  endtask

  // ---- Scalar tests ----

  // Test S1: whole then partial with suspend between
  logic [7:0] s1 = 0;
  always begin
    s1 <= 8'hff;
    do_delay();
    s1[3:0] <= 4'h0;
    #1;
    assert (s1 == 8'hf0) else $fatal(0, "S1 whole->partial: expected f0, got %0h", s1);
  end

  // Test S2: partial then whole with suspend between
  logic [7:0] s2 = 0;
  always begin
    s2[3:0] <= 4'h0;
    do_delay();
    s2 <= 8'hff;
    #1;
    assert (s2 == 8'hff) else $fatal(0, "S2 partial->whole: expected ff, got %0h", s2);
  end

  // Test S3: two partials to non-overlapping ranges
  logic [7:0] s3 = 0;
  always begin
    s3[7:4] <= 4'ha;
    do_delay();
    s3[3:0] <= 4'h5;
    #1;
    assert (s3 == 8'ha5) else $fatal(0, "S3 partial+partial: expected a5, got %0h", s3);
  end

  // Test S4: two partials to same range (last wins)
  logic [7:0] s4 = 0;
  always begin
    s4[3:0] <= 4'ha;
    do_delay();
    s4[3:0] <= 4'h5;
    #1;
    assert (s4 == 8'h05) else $fatal(0, "S4 partial overwrite: expected 05, got %0h", s4);
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
    assert (s5 == 8'hcc) else $fatal(0, "S5 whole-partial-whole: expected cc, got %0h", s5);
  end

  // ---- Unpacked array element tests ----

  // Test A1: whole element then partial element with suspend between
  logic [7:0] a1 [0:3];
  initial for (int i = 0; i < 4; i++) a1[i] = 0;
  always begin
    a1[1] <= 8'hff;
    do_delay();
    a1[1][3:0] <= 4'h0;
    #1;
    assert (a1[1] == 8'hf0) else $fatal(0, "A1 elem->partial: expected f0, got %0h", a1[1]);
  end

  // Test A2: partial element then whole element with suspend between
  logic [7:0] a2 [0:3];
  initial for (int i = 0; i < 4; i++) a2[i] = 0;
  always begin
    a2[2][7:4] <= 4'hf;
    do_delay();
    a2[2] <= 8'h00;
    #1;
    assert (a2[2] == 8'h00) else $fatal(0, "A2 partial->elem: expected 00, got %0h", a2[2]);
  end

  // Test A3: writes to different indices (both should apply)
  logic [7:0] a3 [0:3];
  initial for (int i = 0; i < 4; i++) a3[i] = 0;
  always begin
    a3[0] <= 8'haa;
    do_delay();
    a3[1] <= 8'hbb;
    #1;
    assert (a3[0] == 8'haa) else $fatal(0, "A3 idx0: expected aa, got %0h", a3[0]);
    assert (a3[1] == 8'hbb) else $fatal(0, "A3 idx1: expected bb, got %0h", a3[1]);
  end

  // Test A4: same index overwrite (last wins)
  logic [7:0] a4 [0:3];
  initial for (int i = 0; i < 4; i++) a4[i] = 0;
  always begin
    a4[0] <= 8'haa;
    do_delay();
    a4[0] <= 8'hbb;
    #1;
    assert (a4[0] == 8'hbb) else $fatal(0, "A4 idx overwrite: expected bb, got %0h", a4[0]);
  end

  // ---- Full array assignment tests ----

  // Test F1: full array then element (element write wins for that index)
  logic [7:0] f1 [0:3];
  initial for (int i = 0; i < 4; i++) f1[i] = 0;
  logic [7:0] f1_src [0:3];
  initial begin f1_src[0]=8'h11; f1_src[1]=8'h22; f1_src[2]=8'h33; f1_src[3]=8'h44; end
  always begin
    f1 <= f1_src;
    do_delay();
    f1[1] <= 8'hff;
    #1;
    assert (f1[0] == 8'h11) else $fatal(0, "F1 [0]: expected 11, got %0h", f1[0]);
    assert (f1[1] == 8'hff) else $fatal(0, "F1 [1]: expected ff, got %0h", f1[1]);
    assert (f1[2] == 8'h33) else $fatal(0, "F1 [2]: expected 33, got %0h", f1[2]);
    assert (f1[3] == 8'h44) else $fatal(0, "F1 [3]: expected 44, got %0h", f1[3]);
  end

  // Test F2: element then full array (full array wins)
  logic [7:0] f2 [0:3];
  initial for (int i = 0; i < 4; i++) f2[i] = 0;
  logic [7:0] f2_src [0:3];
  initial begin f2_src[0]=8'h11; f2_src[1]=8'h22; f2_src[2]=8'h33; f2_src[3]=8'h44; end
  always begin
    f2[1] <= 8'hff;
    do_delay();
    f2 <= f2_src;
    #1;
    assert (f2[0] == 8'h11) else $fatal(0, "F2 [0]: expected 11, got %0h", f2[0]);
    assert (f2[1] == 8'h22) else $fatal(0, "F2 [1]: expected 22, got %0h", f2[1]);
    assert (f2[2] == 8'h33) else $fatal(0, "F2 [2]: expected 33, got %0h", f2[2]);
    assert (f2[3] == 8'h44) else $fatal(0, "F2 [3]: expected 44, got %0h", f2[3]);
  end

  // Test F3: full array then partial element (partial wins for that element's bits)
  logic [7:0] f3 [0:3];
  initial for (int i = 0; i < 4; i++) f3[i] = 0;
  logic [7:0] f3_src [0:3];
  initial begin f3_src[0]=8'haa; f3_src[1]=8'hbb; f3_src[2]=8'hcc; f3_src[3]=8'hdd; end
  always begin
    f3 <= f3_src;
    do_delay();
    f3[2][3:0] <= 4'h0;
    #1;
    assert (f3[0] == 8'haa) else $fatal(0, "F3 [0]: expected aa, got %0h", f3[0]);
    assert (f3[1] == 8'hbb) else $fatal(0, "F3 [1]: expected bb, got %0h", f3[1]);
    assert (f3[2] == 8'hc0) else $fatal(0, "F3 [2]: expected c0, got %0h", f3[2]);
    assert (f3[3] == 8'hdd) else $fatal(0, "F3 [3]: expected dd, got %0h", f3[3]);
  end

  // Test F4: partial element then full array (full array wins)
  logic [7:0] f4 [0:3];
  initial for (int i = 0; i < 4; i++) f4[i] = 0;
  logic [7:0] f4_src [0:3];
  initial begin f4_src[0]=8'haa; f4_src[1]=8'hbb; f4_src[2]=8'hcc; f4_src[3]=8'hdd; end
  always begin
    f4[2][3:0] <= 4'hf;
    do_delay();
    f4 <= f4_src;
    #1;
    assert (f4[0] == 8'haa) else $fatal(0, "F4 [0]: expected aa, got %0h", f4[0]);
    assert (f4[1] == 8'hbb) else $fatal(0, "F4 [1]: expected bb, got %0h", f4[1]);
    assert (f4[2] == 8'hcc) else $fatal(0, "F4 [2]: expected cc, got %0h", f4[2]);
    assert (f4[3] == 8'hdd) else $fatal(0, "F4 [3]: expected dd, got %0h", f4[3]);
  end

  initial begin
    #20;
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
