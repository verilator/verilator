// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

task unit_name;
   $write("unit_name = '%m'\n");
endtask

class Cls;
   static task static_name;
      $write("static_name = '%m'\n");
   endtask
   task nonstatic_name;
      $write("nonstatic_name = '%m'\n");
   endtask
endclass : Cls

module t (/*AUTOARG*/);
   initial begin
      Cls c;
      c = new;
      $write("t = '%m'\n");
      unit_name();
      $write("Below results vary with simulator.\n");
      // E.g. '$unit.\Cls::static_name '
      // E.g. '$unit_x.Cls.static_name'
      c.static_name();
      c.nonstatic_name();
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
