// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class LargePool;
  rand int idx;
  bit used[4096];
  constraint c { used[idx] == 1; }
endclass

module t;
  initial begin
    LargePool obj;
    int randomize_result;

    obj = new;
    obj.used[3001] = 1'b1;
    for (int i = 0; i < 20; i++) begin
      randomize_result = obj.randomize();
      `checkd(randomize_result, 1);
      `checkd(obj.idx, 3001);
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
