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
      valid1 = 5;  // valid statement

      pkg::cls::defi invalid;  // invalid statement
      end
   endtask
endmodule

typedef struct packed {
   logic clk /*verilator clocker*/;
   logic data;
} ss_s;

endmodule
