// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

class Cls;
   task bar;
      static int qux;
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
