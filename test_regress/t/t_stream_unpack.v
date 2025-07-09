// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkp(gotv,expv_s) do begin string gotv_s; gotv_s = $sformatf("%p", gotv); if ((gotv_s) != (expv_s)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv_s), (expv_s)); `stop; end end while(0);

typedef enum bit [5:0] {
   A = 6'b111000,
   B = 6,b111111
} enum_t;

module t (/*AUTOARG*/);
   initial begin
      typedef bit [5:0] bit6_t;
      typedef bit bit6_unpacked_t[6];
      bit6_unpacked_t arr;
      bit [1:0] arr2[3];
      bit6_t arr6[1];
      bit6_t [0:0] parr6;
      bit6_t bit6 = 6'b111000;
      bit [5:0] ans;
      bit [2:0][1:0] ans_packed;
      enum_t ans_enum;
      logic [1:0] a [3] = {1, 0, 3};
      logic [1:0] b [3] = {1, 2, 0};
      logic c [4] = {1, 1, 0, 0};
      logic [15:0] d;
      logic [3:0] e [2];
      logic f [8];
      logic [1:0][7:0] g;
      logic [1:0][1:0][3:0] h;
      byte i [];
      longint j;
      int k;
      int l [];
      logic [127:0] m;
      longint n [];
      logic [255:0] o;
      logic [127:0] p[];

      { >> bit {arr}} = bit6;
      `checkp(arr, "'{'h1, 'h1, 'h1, 'h0, 'h0, 'h0} ");

      arr = { >> bit {bit6}};
      `checkp(arr, "'{'h1, 'h1, 'h1, 'h0, 'h0, 'h0} ");

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
      `checkp(arr, "'{'h0, 'h0, 'h0, 'h1, 'h1, 'h1} ");

      arr = { << bit {bit6}};
      `checkp(arr, "'{'h0, 'h0, 'h0, 'h1, 'h1, 'h1} ");

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
      `checkp(arr2, "'{'h3, 'h2, 'h0} ");

      arr2 = { >> bit[1:0] {bit6}};
      `checkp(arr2, "'{'h3, 'h2, 'h0} ");

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
      `checkp(arr2, "'{'h0, 'h2, 'h3} ");

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
      `checkp(arr6, "'{'h38} ");

      arr6 = { >> bit [5:0] {bit6}};
      `checkp(arr6, "'{'h38} ");

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
      `checkp(arr6, "'{'h38} ");

      arr6 = { << bit [5:0] {bit6}};
      `checkp(arr6, "'{'h38} ");

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
      `checkp(e, "'{'h4, 'hd} ");
      `checkp(f, "'{'h1, 'h0, 'h0, 'h0, 'h1, 'h1, 'h0, 'h0} ");

      d = { << 4 {a, b, c}};
      `checkh(d, 16'b1100100011010100);

      { << 2 {e, f}} = d;
      `checkp(e, "'{'h1, 'h7} ");
      `checkp(f, "'{'h0, 'h0, 'h1, 'h0, 'h0, 'h0, 'h1, 'h1} ");

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
      `checkh(p[0], 128'hfadecafedeadbeefabcd0123456789ab);
      `checkh(p[1], 128'habcd0123456789abfadecafedeadbeef);

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
