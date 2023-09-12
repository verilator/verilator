// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);
`define checks(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

typedef enum bit [5:0] {
   A = 6'b111000,
   B = 6,b111111
} enum_t;

module t (/*AUTOARG*/);
   initial begin
      bit arr[];
      bit [1:0] arr2[$];
      bit [5:0] arr6[$];
      string v;
      bit [5:0] bit6 = 6'b111000;
      bit [5:0] ans;
      enum_t ans_enum;

      { >> bit {arr}} = bit6;
      v = $sformatf("%p", arr); `checks(v, "'{'h0, 'h0, 'h0, 'h1, 'h1, 'h1} ");

      ans = { >> bit {arr} };
      `checkh(ans, bit6);

      ans_enum = enum_t'({ >> bit {arr} });
      `checkh(ans_enum, bit6);

      { << bit {arr}} = bit6;
      v = $sformatf("%p", arr); `checks(v, "'{'h1, 'h1, 'h1, 'h0, 'h0, 'h0} ");

      ans = { << bit {arr} };
      `checkh(ans, bit6);

      ans_enum = enum_t'({ << bit {arr} });
      `checkh(ans_enum, bit6);

      { >> bit[1:0] {arr2}} = bit6;
      v = $sformatf("%p", arr2); `checks(v, "'{'h0, 'h2, 'h3} ");

      ans = { >> bit[1:0] {arr2} };
      `checkh(ans, bit6);

      ans_enum = enum_t'({ >> bit[1:0] {arr2} });
      `checkh(ans_enum, bit6);

      { << bit[1:0] {arr2}} = bit6;
      v = $sformatf("%p", arr2); `checks(v, "'{'h3, 'h2, 'h0} ");

      ans = { << bit[1:0] {arr2} };
      `checkh(ans, bit6);

      ans_enum = enum_t'({ << bit[1:0] {arr2} });
      `checkh(ans_enum, bit6);

      { >> bit [5:0] {arr6} } = bit6;
      v = $sformatf("%p", arr6); `checks(v, "'{'h38} ");

      ans = { >> bit[5:0] {arr6} };
      `checkh(ans, bit6);

      ans_enum = enum_t'({ >> bit[5:0] {arr6} });
      `checkh(ans_enum, bit6);

      { << bit [5:0] {arr6} } = bit6;
      v = $sformatf("%p", arr6); `checks(v, "'{'h38} ");

      ans = { << bit[5:0] {arr6} };
      `checkh(ans, bit6);

      ans_enum = enum_t'({ << bit[5:0] {arr6} });
      `checkh(ans_enum, bit6);

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
