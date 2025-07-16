// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkp(gotv,expv_s) do begin string gotv_s; gotv_s = $sformatf("%p", gotv); if ((gotv_s) != (expv_s)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv_s), (expv_s)); `stop; end end while(0);

module t (/*AUTOARG*/);
   string s[] = { "hello", "sad", "sad", "world" };

   initial begin
      int i;
      bit b;

      i = s.sum with (item.len);
      `checkh(i, 10);
      i = s.product with (item.len);
      `checkh(i, 24);
      b = s.sum with (item == "hello");
      `checkh(b, 1'b1);
      b = s.sum with (item == "");
      `checkh(b, 1'b0);
      b = s.product with (item inside {"hello", "sad"});
      `checkh(b, 1'b0);
      b = s.product with (item inside { "hello", "sad", "world" });
      `checkh(b, 1'b1);

      b = s.unknown_bad;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
