// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t;
  always something();

  function void something();
    void'(process::self());
    $write("*-* All Finished *-*\n");
    $finish;
  endfunction
endmodule
