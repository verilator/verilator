// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  class item;
    rand bit [3:0] mode;
    rand bit [7:0] data[4];

    constraint mode_c {
      mode inside {[0:3]};
    }

    constraint data_c {
      foreach (data[i]) {
        solve mode before data[i];
        if (mode == 0)
          data[i] == 8'h00;
        else
          data[i] inside {[8'd1:8'd255]};
      }
    }
  endclass

  initial begin
    static item it = new;
    repeat (20) begin
      `checkd(it.randomize(), 1);
      if (it.mode == 0) begin
        foreach (it.data[i]) begin
          `checkh(it.data[i], 8'h00);
        end
      end
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
