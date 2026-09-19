// DESCRIPTION: Check that a part-select reaching outside the MSB of a vector
// is clipped to the width in writes and returns only the in-range bits in reads.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: $time=%0t got='h%x exp='h%x\n", `__FILE__,`__LINE__, $time, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

module t;

  // We store the select indices in array to avoid constant folding
  integer idx[5] = '{4, 6, 3, 600, 690};

  // Selects of these are constant on both sides, so they are folded
  localparam bit [5:0] P = 6'b101010;

  // For test_insert_other, kept at module scope so they are not folded away
  real rv[1] = '{2.0 ** 147};
  logic [63:0] q[4];
  logic [95:0] rw[2];
  logic [95:0] pa[2];

  initial begin
    bit [5:0] x;
    integer i;

    // verilator lint_off SELRANGE
    x = 'h0;
    x[8:4] = 5'b10001;
    `checkh(x, 6'b010000);  // Const, partially OOB high

    x = 'h0;
    x[11:6] = 6'b111111;
    `checkh(x, '0);  // Const, fully OOB high

    x = 'h0;
    x[9:3] = 7'b1011010;
    `checkh(x, 6'b010000);  // Const, select width > declared width, OOB high

    i = idx[0];  // 4
    x = 'h0;
    x[i+:5] = 5'b10001;
    `checkh(x, 6'b010000);  // Var, partially OOB high

    i = idx[1];  // 6
    x = 'h0;
    x[i+:6] = 6'b111111;
    `checkh(x, '0);  // Var, fully OOB high

    i = idx[2];  // 3
    x = 'h0;
    x[i+:7] = 7'b1011010;
    `checkh(x, 6'b010000);  // Var, select width > declared width, OOB high
    // verilator lint_on SELRANGE

    test_wide();
    test_read();
    test_param();
    test_insert_other();

    $write("*-* All finished *-*\n");
    $finish;
  end

  // Writes that go out of range are clipped properly
  // This tests both WW and WQ assign selects
  task automatic test_wide();
    bit [703:0] w[2];  // 22 words each
    bit [255:0] d;
    bit [63:0] d64;
    integer i;
    begin
      d = {8{32'hdead_beef}};
      d64 = 64'hdead_beef_feed_face;

      // verilator lint_off SELRANGE
      // Wide source, 855:600 requested but only 703:600 exist (VL_ASSIGNSEL_WW)
      i = idx[3];  // 600
      w = '{default: '0};
      w[0][i+:256] = d;
      `checkh(w[0][703:600], d[103:0]);
      `checkh(w[0][599:0], '0);
      `checkh(w[1], '0);

      // Quad source, 753:690 requested but only 703:690 exist (VL_ASSIGNSEL_WQ)
      i = idx[4];  // 690
      w = '{default: '0};
      w[0][i+:64] = d64;
      `checkh(w[0][703:690], d64[13:0]);
      `checkh(w[0][689:0], '0);
      `checkh(w[1], '0);
      // verilator lint_on SELRANGE
    end
  endtask

  // Reads that go out of range are clipped properly and have 0's in the OOB bits
  // This tests both wide reads and narrowing reads.
  task automatic test_read();
    bit [703:0] mem[2];
    bit [255:0] r256;
    bit [63:0] r64;
    integer i;
    begin
      mem[0] = '1;
      mem[1] = '1;

      // verilator lint_off SELRANGE
      // Wide result, reads mem[0] word by word (expandWide)
      i = idx[3];  // 600
      r256 = mem[0][i+:256];
      `checkh(r256, {{152{1'b0}}, {104{1'b1}}});

      // Quad result, reads the words holding lsb, lsb+31 and lsb+63 (visit)
      i = idx[4];  // 690
      r64 = mem[0][i+:64];
      `checkh(r64, {{50{1'b0}}, {14{1'b1}}});
      // verilator lint_on SELRANGE
    end
  endtask

  // Validates reads where both ends are constant.
  task automatic test_param();
    begin
      // verilator lint_off SELRANGE
      `checkh(P[8:4], 5'b00010);  // Partially OOB high
      `checkh(P[11:6], 6'b000000);  // Fully OOB high
      // verilator lint_on SELRANGE
    end
  endtask

  // Validates two special cases involving real to integer conversion and 
  // stream packing
  task automatic test_insert_other();
    integer k;
    begin
      // Real to a 96 bit integer.  The mantissa is 53 bits, so a start bit of
      // 95 reaches bit 147 unless clipped.
      rw = '{default: '0};
      /* verilator lint_off REALCVT */
      rw[0] = rv[0];
      /* verilator lint_on REALCVT */
      `checkh(rw[0], '0);

      // Streaming 4 x 64 bits into a 96 bit target, so the source does not fit
      for (k = 0; k < 4; k++) q[k] = 64'hdead_beef_cafe_f00d;
      pa = '{default: '0};
      /* verilator lint_off WIDTHTRUNC */
      pa[0] = {>>{q}};
      /* verilator lint_on WIDTHTRUNC */
      `checkh(pa[0], '0);
    end
  endtask
endmodule
