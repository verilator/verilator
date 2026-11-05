// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  int x;

  task automatic report(input int v);
  endtask

  task automatic report_output(output int v);
  endtask

  initial begin
    assert #0 (0)
    else begin
      report(1);
    end

    assert #0 (0)
    else x = 1;
    assert #0 (0)
    else if (x[0]) report(2);
    assert #0 (0)
    else x++;
    assert #0 (0)
    else report_output(x);
  end
endmodule
