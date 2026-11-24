// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  int dyn[];
  int q[$];

  task automatic report_ref(ref int r);
  endtask

  task automatic report_queue_ref(ref int r[$]);
  endtask

  initial begin
    automatic int a;
    assert #0 (0)
    else report_ref(a);
  end

  initial begin
    dyn = new[1];
    q.push_back(0);
    assert #0 (0)
    else report_ref(dyn[0]);
    assert #0 (0)
    else report_ref(q[0]);
    assert #0 (0)
    else report_queue_ref(q);
  end
endmodule
