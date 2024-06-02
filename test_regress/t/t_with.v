// DESCRIPTION: Verilator: Verilog Test module for SystemVerilog 'alias'
//
// Simple bi-directional alias test.
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t (/*AUTOARG*/);

   initial begin
      int tofind;
      int aliases[$];
      int found[$];
      int i;
      byte byteq[$] = {2, -1, 127};

      aliases = '{ 1, 4, 6, 8};
      tofind = 6;
      found = aliases.find with (item == 1);
      `checkh(found.size, 1);
      found = aliases.find(j) with (j == tofind);
      `checkh(found.size, 1);
      // And as function
      aliases.find(i) with (i == tofind);

      // No parenthesis
      tofind = 0;
      found = aliases.find with (item == tofind);
      `checkh(found.size, 0);
      aliases.find with (item == tofind);

      // bug3387
      i = aliases.sum();
      `checkh(i, 'h13);
      i = byteq.sum() with (int'(item));
      `checkh(i, 128);

      // Unique (array method)
      tofind = 4;
      found = aliases.find with (tofind);  // "true" match
      `checkh(found.size, 4);
      found = aliases.find() with (item == tofind);
      `checkh(found.size, 1);
      found = aliases.find(i) with (i == tofind);
      `checkh(found.size, 1);
      i = aliases.or(v) with (v);
      `checkh(i, 'hf);
      i = aliases.and(v) with (v);
      `checkh(i, 0);
      i = aliases.xor(v) with (v);
      `checkh(i, 'hb);

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
