// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Tudor Timi.
// SPDX-License-Identifier: CC0-1.0

class svunit_base;
   function new(string name);
   endfunction
endclass

class svunit_testcase extends svunit_base;
   function new(string name);
      super.new(name);
   endfunction
endclass

module dut_unit_test;
   svunit_testcase svunit_ut = new("dut_ut");
endmodule

module t(/*AUTOARG*/);

   dut_unit_test dut_ut();

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
