// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

module t;

  // Comparison results shifted into the sign bit, then shifted back down
  function automatic logic [31:0] expShift(logic c, logic [4:0] n);
    return c ? 32'h8000_0000 >> n : 32'h0;
  endfunction
  function automatic logic [63:0] expShift64(logic c, logic [5:0] m);
    return c ? 64'h8000_0000_0000_0000 >> m : 64'h0;
  endfunction

  initial begin
    logic [63:0] crc;
    logic [12:0] a;
    logic [12:0] b;
    logic [4:0] n;
    logic [5:0] m;
    logic s;
    real ra;
    real rb;
    string sa;
    string sb;
    crc = 64'h5aef0c8d_d70a4497;
    repeat (100) begin
      crc = {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
      a = 13'(crc[1:0]);
      b = 13'(crc[3:2]);
      n = crc[8:4];
      m = crc[15:10];
      s = crc[9];
      ra = a;
      rb = b;
      sa = a[0] ? "x" : "y";
      sb = b[0] ? "x" : "y";
      `checkh((32'(a < b) << 31) >> n, expShift(a < b, n));
      `checkh((32'(a <= b) << 31) >> n, expShift(a <= b, n));
      `checkh((32'(a > b) << 31) >> n, expShift(a > b, n));
      `checkh((32'(a >= b) << 31) >> n, expShift(a >= b, n));
      `checkh((32'(a == b) << 31) >> n, expShift(a == b, n));
      `checkh((32'(a != b) << 31) >> n, expShift(a != b, n));
      // verilator lint_off WIDTHTRUNC
      `checkh((32'(!a) << 31) >> n, expShift(!a, n));
      `checkh((32'(a && b) << 31) >> n, expShift(a && b, n));
      `checkh((32'(a || b) << 31) >> n, expShift(a || b, n));
      // verilator lint_on WIDTHTRUNC
      `checkh((32'(s ? a < b : a > b) << 31) >> n, expShift(s ? a < b : a > b, n));
      `checkh((32'(ra > rb) << 31) >> n, expShift(ra > rb, n));
      `checkh((32'(!ra) << 31) >> n, expShift(!ra, n));
      `checkh((32'(ra && rb) << 31) >> n, expShift(ra && rb, n));
      `checkh((32'(ra || rb) << 31) >> n, expShift(ra || rb, n));
      `checkh((32'(sa == sb) << 31) >> n, expShift(sa == sb, n));
      `checkh((64'(a < b) << 63) >> m, expShift64(a < b, m));
      `checkh((64'(a <= b) << 63) >> m, expShift64(a <= b, m));
      `checkh((64'(a > b) << 63) >> m, expShift64(a > b, m));
      `checkh((64'(a >= b) << 63) >> m, expShift64(a >= b, m));
      `checkh((64'(a == b) << 63) >> m, expShift64(a == b, m));
      `checkh((64'(a != b) << 63) >> m, expShift64(a != b, m));
      // verilator lint_off WIDTHTRUNC
      `checkh((64'(!a) << 63) >> m, expShift64(!a, m));
      `checkh((64'(a && b) << 63) >> m, expShift64(a && b, m));
      `checkh((64'(a || b) << 63) >> m, expShift64(a || b, m));
      // verilator lint_on WIDTHTRUNC
      `checkh((64'(s ? a < b : a > b) << 63) >> m, expShift64(s ? a < b : a > b, m));
      `checkh((64'(ra > rb) << 63) >> m, expShift64(ra > rb, m));
      `checkh((64'(!ra) << 63) >> m, expShift64(!ra, m));
      `checkh((64'(ra && rb) << 63) >> m, expShift64(ra && rb, m));
      `checkh((64'(ra || rb) << 63) >> m, expShift64(ra || rb, m));
      `checkh((64'(sa == sb) << 63) >> m, expShift64(sa == sb, m));
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
