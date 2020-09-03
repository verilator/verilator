// DESCRIPTION: Verilator: Verilog Test module for SystemVerilog 'alias'
//
// Simple bi-directional alias test.
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   initial begin
      int tofind;
      int aliases[$];
      int found[$];
      int id;
      int i;
      aliases = '{ 1, 4, 6, 8};
      tofind = 6;
      found = aliases.find(i) with (i == to_find);
      // And as function
      aliases.find(i) with (i == to_find);

      // No parenthesis
      found = aliases.find with (item == i);
      aliases.find with (item == i);

      // Unique (array method)
      id = 4;
      found = aliases.unique with (id);
      found = aliases.unique() with (id);
      found = aliases.unique(i) with (id);
      found = aliases.or with (id);
      found = aliases.and with (id);
      found = aliases.xor with (id);
   end

endmodule
