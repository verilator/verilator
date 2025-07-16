// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Dan Petrisko.
// SPDX-License-Identifier: CC0-1.0

package pkg;
   class cls;
      typedef unknown defu;
      typedef int defi;
   endclass
endpackage

module t;
   task tsk;
      begin
      Invalid1 invalid1;  // invalid declaration
      pkg::cls::defi valid1;  // valid declaration
      pkg::cls::defu valid2;  // valid declaration
      Invalid2 invalid2;  // invalid declaration
      end
   endtask
endmodule
