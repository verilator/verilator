// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under The Creative Commons Public Domain, for
// any use, without warranty, 2021 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

timeunit 10ps;
timeprecision 10ps;

task show;
   $printtimescale;
endtask

module from_unit;
   task show;
      $printtimescale;
   endtask
endmodule

module t;
   from_unit from_unit();
   timeunit 100ps;
   initial begin
      show();
      from_unit.show();
      $printtimescale;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
