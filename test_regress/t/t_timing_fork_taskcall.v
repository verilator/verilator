// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t;
  task foo;
    #1 if ($time != 1) $stop;
    #1 if ($time != 2) $stop;
    #1 if ($time != 3) $stop;
  endtask

  initial fork
    foo;
    foo;
    foo;
    #4 begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  join
endmodule
