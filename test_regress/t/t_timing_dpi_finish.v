// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Antmicro.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t;
  import "DPI-C" context task imp();
  export "DPI-C" task ex;
  export "DPI-C" function bump;
  int cnt = 0;

  task automatic ex();
    #100;
  endtask

  function void bump();
    cnt++;
  endfunction

  // The model is destroyed while imp() is still waiting for ex().
  initial imp();
  initial #5 $finish;

  final begin
    `checkd(cnt, 0);
    $write("*-* All Finished *-*\n");
  end
endmodule
