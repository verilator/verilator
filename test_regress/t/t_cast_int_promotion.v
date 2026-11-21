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

  typedef struct {
    logic [14:0] g;
  } s_t;

  class C;
    logic [6:0] f;
  endclass

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
    logic [12:0] ua[2];
    logic [12:0] ub[2];
    logic [2:0] x;
    logic [69:0] wa;
    logic [69:0] wb;
    logic signed [69:0] swa;
    logic signed [69:0] swb;
    logic [1:0] i;
    logic [6:0] arr7[4];
    logic [14:0] arr15[4];
    logic [6:0] aa7[logic [1:0]];
    logic [6:0] wc7[*];
    logic [6:0] q7[$];
    s_t sarr[2];
    C c;
    real ra;
    real rb;
    string sa;
    string sb;
    crc = 64'h5aef0c8d_d70a4497;
    c = new;
    repeat (100) begin
      crc = {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
      a = 13'(crc[1:0]);
      b = 13'(crc[3:2]);
      n = crc[8:4];
      m = crc[15:10];
      s = crc[9];
      ua = '{a, b};
      ub = '{b, a};
      x = crc[18:16];
      wa = {crc[19], 69'(a)};
      wb = {crc[20], 69'(b)};
      swa = wa;
      swb = wb;
      i = crc[22:21];
      arr7[i] = crc[29:23];
      arr15[i] = crc[44:30];
      aa7[i] = crc[29:23];
      wc7[i] = crc[29:23];
      q7 = {crc[29:23]};
      sarr[s].g = crc[44:30];
      c.f = crc[29:23];
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
      // Unpacked array compares become '&&'/'||' of element compares
      `checkh((32'(ua == ub) << 31) >> n, expShift(a == b, n));
      `checkh((32'(ua != ub) << 31) >> n, expShift(a != b, n));
      `checkh((32'(s ? a < b : a > b) << 31) >> n, expShift(s ? a < b : a > b, n));
      `checkh((32'(ra == rb) << 31) >> n, expShift(ra == rb, n));
      `checkh((32'(ra < rb) << 31) >> n, expShift(ra < rb, n));
      `checkh((32'(ra <= rb) << 31) >> n, expShift(ra <= rb, n));
      `checkh((32'(ra > rb) << 31) >> n, expShift(ra > rb, n));
      `checkh((32'(ra >= rb) << 31) >> n, expShift(ra >= rb, n));
      `checkh((32'(!ra) << 31) >> n, expShift(!ra, n));
      `checkh((32'(ra && rb) << 31) >> n, expShift(ra && rb, n));
      `checkh((32'(ra || rb) << 31) >> n, expShift(ra || rb, n));
      `checkh((32'(sa == sb) << 31) >> n, expShift(sa == sb, n));
      `checkh((32'(sa != sb) << 31) >> n, expShift(sa != sb, n));
      `checkh((32'(sa < sb) << 31) >> n, expShift(sa < sb, n));
      `checkh((32'(sa <= sb) << 31) >> n, expShift(sa <= sb, n));
      `checkh((32'(sa > sb) << 31) >> n, expShift(sa > sb, n));
      `checkh((32'(sa >= sb) << 31) >> n, expShift(sa >= sb, n));
      `checkh((32'(&x) << 31) >> n, expShift(&x, n));
      `checkh((32'(|x) << 31) >> n, expShift(|x, n));
      `checkh((32'(wa != wb) << 31) >> n, expShift(wa != wb, n));
      `checkh((32'(wa < wb) << 31) >> n, expShift(wa < wb, n));
      `checkh((32'(wa <= wb) << 31) >> n, expShift(wa <= wb, n));
      `checkh((32'(wa > wb) << 31) >> n, expShift(wa > wb, n));
      `checkh((32'(wa >= wb) << 31) >> n, expShift(wa >= wb, n));
      `checkh((32'(swa < swb) << 31) >> n, expShift(swa < swb, n));
      `checkh((32'(swa <= swb) << 31) >> n, expShift(swa <= swb, n));
      `checkh((32'(swa > swb) << 31) >> n, expShift(swa > swb, n));
      `checkh((32'(swa >= swb) << 31) >> n, expShift(swa >= swb, n));
      // Other operators also turn a C++ 'bool' into a negative 'int'
      `checkh((~32'(a < b)) >> n, (a < b ? 32'hffff_fffe : 32'hffff_ffff) >> n);
      `checkh((32'(a < b) - 32'(a > b)) >> n, (a < b ? 32'h1 : a > b ? 32'hffff_ffff : 32'h0) >> n);
      `checkh({32{a < b}} >> n, (a < b ? 32'hffff_ffff : 32'h0) >> n);
      // Elements and members narrower than 'int' are C++ 'CData'/'SData', which promote too
      `checkh((32'(arr7[i]) << 25) >> n, {crc[29:23], 25'h0} >> n);
      `checkh((32'(arr15[i]) << 17) >> n, {crc[44:30], 17'h0} >> n);
      `checkh((32'(aa7[i]) << 25) >> n, {crc[29:23], 25'h0} >> n);
      `checkh((32'(wc7[i]) << 25) >> n, {crc[29:23], 25'h0} >> n);
      `checkh((32'(q7[0]) << 25) >> n, {crc[29:23], 25'h0} >> n);
      `checkh((32'(sarr[s].g) << 17) >> n, {crc[44:30], 17'h0} >> n);
      `checkh((32'(c.f) << 25) >> n, {crc[29:23], 25'h0} >> n);
      // Methods might return C++ 'int'
      `checkh((q7.size() << 31) >> n, 32'h8000_0000 >> n);
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
