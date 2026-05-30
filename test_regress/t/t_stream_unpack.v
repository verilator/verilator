// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkp(gotv,expv_s) do begin string gotv_s; gotv_s = $sformatf("%p", gotv); if ((gotv_s) != (expv_s)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv_s), (expv_s)); `stop; end end while(0);
// verilog_format: on

typedef enum bit [5:0] {
  A = 6'b111000,
  B = 6,b111111
} enum_t;

module t;
  initial begin
    typedef bit [5:0] bit6_t;
    typedef bit bit6_unpacked_t[6];
    automatic bit6_unpacked_t arr;
    automatic bit [1:0] arr2[3];
    automatic bit6_t arr6[1];
    automatic bit6_t [0:0] parr6;
    automatic bit6_t bit6 = 6'b111000;
    automatic bit [5:0] ans;
    automatic bit [2:0][1:0] ans_packed;
    automatic enum_t ans_enum;
    automatic logic [1:0] a [3] = {1, 0, 3};
    automatic logic [1:0] b [3] = {1, 2, 0};
    automatic logic c [4] = {1, 1, 0, 0};
    automatic logic [15:0] d;
    automatic logic [3:0] e [2];
    automatic logic f [8];
    automatic logic [1:0][7:0] g;
    automatic logic [1:0][1:0][3:0] h;
    automatic byte i [];
    automatic longint j;
    automatic int k;
    automatic int l [];
    automatic logic [127:0] m;
    automatic longint n [];
    automatic logic [255:0] o;
    automatic logic [127:0] p[];

    { >> bit {arr}} = bit6;
    `checkp(arr, "'{'h1, 'h1, 'h1, 'h0, 'h0, 'h0}");

    arr = { >> bit {bit6}};
    `checkp(arr, "'{'h1, 'h1, 'h1, 'h0, 'h0, 'h0}");

    ans = { >> bit {arr} };
    `checkh(ans, bit6);

    { >> bit {ans}} = arr;
    `checkh(ans, bit6);

    ans_packed = { >> bit {arr} };
    `checkh(ans_packed, bit6);

    { >> bit {ans_packed}} = arr;
    `checkh(ans_packed, bit6);

    ans_enum = enum_t'({ >> bit {arr} });
    `checkh(ans_enum, bit6);

    { << bit {arr}} = bit6;
    `checkp(arr, "'{'h0, 'h0, 'h0, 'h1, 'h1, 'h1}");

    arr = { << bit {bit6}};
    `checkp(arr, "'{'h0, 'h0, 'h0, 'h1, 'h1, 'h1}");

    ans = { << bit {arr} };
    `checkh(ans, bit6);

    { << bit {ans} } = arr;
    `checkh(ans, bit6);

    ans_packed = { << bit {arr} };
    `checkh(ans_packed, bit6);

    { << bit {ans_packed} } = arr;
    `checkh(ans_packed, bit6);

    ans_enum = enum_t'({ << bit {arr} });
    `checkh(ans_enum, bit6);

    { >> bit[1:0] {arr2}} = bit6;
    `checkp(arr2, "'{'h3, 'h2, 'h0}");

    arr2 = { >> bit[1:0] {bit6}};
    `checkp(arr2, "'{'h3, 'h2, 'h0}");

    ans = { >> bit[1:0] {arr2} };
    `checkh(ans, bit6);

    { >> bit[1:0] {ans} } = arr2;
    `checkh(ans, bit6);

    ans_packed = { >> bit[1:0] {arr2} };
    `checkh(ans_packed, bit6);

    { >> bit[1:0] {ans_packed} } = arr2;
    `checkh(ans_packed, bit6);

    ans_enum = enum_t'({ >> bit[1:0] {arr2} });
    `checkh(ans_enum, bit6);

    { << bit[1:0] {arr2}} = bit6;
    `checkp(arr2, "'{'h0, 'h2, 'h3}");

    ans = { << bit[1:0] {arr2} };
    `checkh(ans, bit6);

    { << bit[1:0] {ans} } = arr2;
    `checkh(ans, bit6);

    ans_packed = { << bit[1:0] {arr2} };
    `checkh(ans_packed, bit6);

    { << bit[1:0] {ans_packed} } = arr2;
    `checkh(ans_packed, bit6);

    ans_enum = enum_t'({ << bit[1:0] {arr2} });
    `checkh(ans_enum, bit6);

    { >> bit [5:0] {arr6} } = bit6;
    `checkp(arr6, "'{'h38}");

    arr6 = { >> bit [5:0] {bit6}};
    `checkp(arr6, "'{'h38}");

    ans = { >> bit[5:0] {arr6} };
    `checkh(ans, bit6);

    { >> bit[5:0] {ans} } = arr6;
    `checkh(ans, bit6);

    ans_packed = { >> bit[5:0] {arr6} };
    `checkh(ans_packed, bit6);

    { >> bit[5:0] {ans_packed} } = arr6;
    `checkh(ans_packed, bit6);

    ans_enum = enum_t'({ >> bit[5:0] {arr6} });
    `checkh(ans_enum, bit6);

    { << bit [5:0] {arr6} } = bit6;
    `checkp(arr6, "'{'h38}");

    arr6 = { << bit [5:0] {bit6}};
    `checkp(arr6, "'{'h38}");

    ans = { << bit[5:0] {arr6} };
    `checkh(ans, bit6);

    { << bit[5:0] {ans} } = arr6;
    `checkh(ans, bit6);

    ans_packed = { << bit[5:0] {arr6} };
    `checkh(ans_packed, bit6);

    { << bit[5:0] {ans_packed} } = arr6;
    `checkh(ans_packed, bit6);

    ans_enum = enum_t'({ << bit[5:0] {arr6} });
    `checkh(ans_enum, bit6);

    { >> bit [5:0] {parr6} } = bit6;
    `checkh(parr6, bit6);

    parr6 = { >> bit [5:0] {bit6}};
    `checkh(parr6, bit6);

    ans = { >> bit[5:0] {parr6} };
    `checkh(ans, bit6);

    { >> bit[5:0] {ans} } = parr6;
    `checkh(ans, bit6);

    ans_packed = { >> bit[5:0] {parr6} };
    `checkh(ans_packed, bit6);

    { >> bit[5:0] {ans_packed} } = parr6;
    `checkh(ans_packed, bit6);

    ans_enum = enum_t'({ >> bit[5:0] {parr6} });
    `checkh(ans_enum, bit6);

    { << bit [5:0] {parr6} } = bit6;
    `checkh(parr6, bit6);

    parr6 = { << bit [5:0] {bit6}};
    `checkh(parr6, bit6);

    ans = { << bit[5:0] {parr6} };
    `checkh(ans, bit6);

    { << bit[5:0] {ans} } = parr6;
    `checkh(ans, bit6);

    ans_packed = { << bit[5:0] {parr6} };
    `checkh(ans_packed, bit6);

    { << bit[5:0] {ans_packed} } = parr6;
    `checkh(ans_packed, bit6);

    ans_enum = enum_t'({ << bit[5:0] {parr6} });
    `checkh(ans_enum, bit6);

    d = { >> {a, b, c}};
    `checkh(d, 16'b0100110110001100);

    { >> {e, f}} = d;
    `checkp(e, "'{'h4, 'hd}");
    `checkp(f, "'{'h1, 'h0, 'h0, 'h0, 'h1, 'h1, 'h0, 'h0}");

    d = { << 4 {a, b, c}};
    `checkh(d, 16'b1100100011010100);

    { << 2 {e, f}} = d;
    `checkp(e, "'{'h1, 'h7}");
    `checkp(f, "'{'h0, 'h0, 'h1, 'h0, 'h0, 'h0, 'h1, 'h1}");

    g = { << 8 {16'hABCD}};
    `checkh(g, 16'hCDAB);

    h = { << 8 {16'hABCD}};
    `checkh(h, 16'hCDAB);

    i = new[8]('{8'hfa, 8'hde, 8'hca, 8'hfe,
             8'hde, 8'had, 8'hbe, 8'hef});
    `checkh(i[0], 8'hfa);
    `checkh(i[7], 8'hef);
    j = {>>{i}};
    `checkh(j, 64'hfadecafedeadbeef);
    j = {<<8{i}};
    `checkh(j, 64'hefbeaddefecadefa);

    i = new[4]('{8'hba, 8'hbe, 8'hfa, 8'hce});
    k = {>>{i}};
    `checkh(k, 32'hbabeface);
    k = {<<8{i}};
    `checkh(k, 32'hcefabeba);

    i = new[8]('{8'hba, 8'hbe, 8'hfa, 8'hce, 8'hde, 8'had, 8'hbe, 8'hef});
    j = {>>{i}};
    `checkh(j, 64'hbabefacedeadbeef);
    j = {<<8{i}};
    `checkh(j, 64'hefbeaddecefabeba);

    i = new[16]('{8'hba, 8'hbe, 8'hfa, 8'hce, 8'hde, 8'had, 8'hbe, 8'hef,
              8'hde, 8'had, 8'hbe, 8'hef, 8'hde, 8'had, 8'hbe, 8'hef});
    m = {>>{i}};
    `checkh(m, 128'hbabefacedeadbeefdeadbeefdeadbeef);
    m = {<<8{i}};
    `checkh(m, 128'hefbeaddeefbeaddeefbeaddecefabeba);

    l = new[2]('{32'hbabeface, 32'hdeadbeef});
    j = {>>{l}};
    `checkh(j, 64'hbabefacedeadbeef);
    j = {<<8{l}};
    `checkh(j, 64'hefbeaddecefabeba);

    l = new[4]('{32'hbabeface, 32'hdeadbeef, 32'hdeadbeef, 32'hdeadbeef});
    m = {>>{l}};
    `checkh(m, 128'hbabefacedeadbeefdeadbeefdeadbeef);
    m = {<<8{l}};
     `checkh(m, 128'hefbeaddeefbeaddeefbeaddecefabeba);

    n = new[2]('{64'hfadecafedeadbeef, 64'habcd0123456789ab});
    m = {>>{n}};
    `checkh(m, 128'hfadecafedeadbeefabcd0123456789ab);
    m = {<<64{n}};
    `checkh(m, 128'habcd0123456789abfadecafedeadbeef);

    p = new[2]('{128'hfadecafedeadbeefabcd0123456789ab,
             128'habcd0123456789abfadecafedeadbeef});
    o = {>>{p}};
    `checkh(o, 256'hfadecafedeadbeefabcd0123456789ababcd0123456789abfadecafedeadbeef);
    o = {<<128{p}};
    `checkh(o, 256'habcd0123456789abfadecafedeadbeeffadecafedeadbeefabcd0123456789ab);
    {>>{p}} = o;
    `checkh(p[0], 128'habcd0123456789abfadecafedeadbeef);
    `checkh(p[1], 128'hfadecafedeadbeefabcd0123456789ab);

    begin
      automatic logic arr2d_1 [2][2];
      automatic logic [3:0] packed_4;

      // Right-side test (unpack)
      packed_4 = 4'b1100;
      arr2d_1 = { >> {packed_4}};
      `checkh(arr2d_1[0][0], 1'b1);
      `checkh(arr2d_1[0][1], 1'b1);
      `checkh(arr2d_1[1][0], 1'b0);
      `checkh(arr2d_1[1][1], 1'b0);

      // Left-side test (pack)
      arr2d_1[0][0] = 1'b0;
      arr2d_1[0][1] = 1'b1;
      arr2d_1[1][0] = 1'b0;
      arr2d_1[1][1] = 1'b1;
      { >> {packed_4}} = arr2d_1;
      `checkh(packed_4, 4'b0101);

      // Constant source test
      arr2d_1 = { >> {4'b1010}};
      `checkh(arr2d_1[0][0], 1'b1);
      `checkh(arr2d_1[0][1], 1'b0);
      `checkh(arr2d_1[1][0], 1'b1);
      `checkh(arr2d_1[1][1], 1'b0);

      // 3D Test
      begin
        automatic logic arr3d_1 [2][2][2];
        automatic logic [7:0] packed_8;

        packed_8 = 8'b1100_1010;
        arr3d_1 = { >> {packed_8}};
        `checkh(arr3d_1[0][0][0], 1'b1);
        `checkh(arr3d_1[0][0][1], 1'b1);
        `checkh(arr3d_1[0][1][0], 1'b0);
        `checkh(arr3d_1[0][1][1], 1'b0);
        `checkh(arr3d_1[1][0][0], 1'b1);
        `checkh(arr3d_1[1][0][1], 1'b0);
        `checkh(arr3d_1[1][1][0], 1'b1);
        `checkh(arr3d_1[1][1][1], 1'b0);

        packed_8 = 8'h0;
        { >> {packed_8}} = arr3d_1;
        `checkh(packed_8, 8'b1100_1010);
      end

      // 48-bit Test (tests VL_UNPACK_UI_Q)
      begin
        automatic logic [47:0] packed_48;
        automatic logic [11:0] arr2d_12 [2][2];

        packed_48 = 48'habcdef_012345;
        arr2d_12 = { >> {packed_48}};
        `checkh(arr2d_12[0][0], 12'habc);
        `checkh(arr2d_12[0][1], 12'hdef);
        `checkh(arr2d_12[1][0], 12'h012);
        `checkh(arr2d_12[1][1], 12'h345);
      end

      // 96-bit Test (tests VL_UNPACK_UI_W)
      begin
        automatic logic [95:0] packed_96;
        automatic logic [23:0] arr2d_24 [2][2];

        packed_96 = 96'h123456_789abc_def012_345678;
        arr2d_24 = { >> {packed_96}};
        `checkh(arr2d_24[0][0], 24'h123456);
        `checkh(arr2d_24[0][1], 24'h789abc);
        `checkh(arr2d_24[1][0], 24'hdef012);
        `checkh(arr2d_24[1][1], 24'h345678);
      end

      // 2D Array of QData (64-bit) Elements Test
      begin
        automatic logic [127:0] packed_128;
        automatic logic [63:0] arr2d_q [1][2];

        packed_128 = 128'hfadecafedeadbeef_abcd0123456789ab;
        arr2d_q = { >> {packed_128}};
        `checkh(arr2d_q[0][0], 64'hfadecafedeadbeef);
        `checkh(arr2d_q[0][1], 64'habcd0123456789ab);
      end

      // 2D Array of Wide (96-bit) Elements Test
      begin
        automatic logic [191:0] packed_192;
        automatic logic [95:0] arr2d_w [1][2];

        packed_192 = 192'h123456789abcdef012345678_9abcdef01234567812345678;
        arr2d_w = { >> {packed_192}};
        `checkh(arr2d_w[0][0], 96'h123456789abcdef012345678);
        `checkh(arr2d_w[0][1], 96'h9abcdef01234567812345678);
      end
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
