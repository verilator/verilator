// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

class Cls;
   task bar;
      int qux;
      qux <= '1;
   endtask
endclass

module t;
   initial begin
      Cls c;
      c.bar();
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
