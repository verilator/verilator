// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  class item;
    rand int unsigned arr[4];
    rand int unsigned wgt_zero;
    rand int unsigned wgt_nonzero;

    constraint wgt_c {
      wgt_zero inside {[1:10]};
      wgt_nonzero inside {[1:10]};
    }

    constraint dist_foreach_c {
      foreach (arr[i]) {
        arr[i] dist {0 :/ wgt_zero, [1:15] :/ wgt_nonzero};
      }
    }
  endclass

  initial begin
    static item it = new;
    repeat (20) begin
      `checkd(it.randomize(), 1);
      foreach (it.arr[i]) begin
        `checkd(it.arr[i] <= 32'd15, 1);
      end
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
