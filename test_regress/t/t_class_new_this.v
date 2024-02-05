// DESCRIPTION: Verilator: Verilog Test module
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

interface class ICls;
   pure virtual function string get();
endclass

class Cls;
   string name;
   ICls icls;
   function new(string name, ICls icls);
      this.name = name;
      this.icls = icls;
   endfunction
endclass

class Testcase implements ICls;
   Cls cls = new("test_class", this);
   virtual function string get();
      return "In ICls";
   endfunction
endclass

module t(/*AUTOARG*/);

   initial begin
      Testcase test;
      test = new;
      if (test.cls.name != "test_class") $stop;
      if (test.cls.icls.get() != "In ICls") $stop;
      test.cls.icls = null; // Prevent leak
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
