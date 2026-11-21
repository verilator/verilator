// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

`ifdef TEST_IMPURE_ENDPOINT
module t (input clk);
  logic start = 0;
  logic a = 1;
  int calls = 0;

  function logic endpoint();
    calls++;
    return 0;
  endfunction

  // Bad: functions in assertion Boolean expressions must not have side effects.
  assert property (@(posedge clk) start |-> a[*1:$] ##0 endpoint());
endmodule
`else
module t (input clk);
  logic a;
  int n;

  // Bad: non-constant repetition count
  assert property (@(posedge clk) a [*n] |-> 1);

  // Bad: [*0] unsupported exact zero repetition
  assert property (@(posedge clk) a [*0] |-> 1);

  // Bad: max count < min count
  assert property (@(posedge clk) a [*3:1] |-> 1);

  // Bad: non-constant max count
  assert property (@(posedge clk) a [*1:n] |-> 1);

  // Bad: [*N:0] zero max count
  assert property (@(posedge clk) a [*0:0] |-> 1);

  // Bad: negative unbounded minimum
  assert property (@(posedge clk) a [*-1:$] |-> 1);

  // Bad: non-constant unbounded minimum
  assert property (@(posedge clk) a [*n:$] |-> 1);

endmodule
`endif
