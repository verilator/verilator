// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  int cyc = 0;
  logic a = 0;

  // Side effects in property and sequence expressions are not allowed (IEEE 1800-2023 16.6)
  assert property (@(posedge clk) a |=> ($urandom % 3) < 3);
  cover property (@(posedge clk) (($urandom % 4) == 1) ##1 a);
  sequence s_rep;
    @(posedge clk) ($random % 2 == 0) [*2];
  endsequence
  cover property (s_rep);

  // Sampled value functions may evaluate their expression again
  assert property (@(posedge clk) $past($urandom % 2) < 2);
  assert property (@(posedge clk) $rose(1'($urandom)) |-> 1);
  assert property (@(posedge clk) $fell(1'($urandom)) |-> 1);
  assert property (@(posedge clk) $stable(1'($urandom)) |-> 1);
  // Or a function call without side effects, with a default argument
  function automatic int add2(int x, int y = 2);
    return x + y;
  endfunction
  assert property (@(posedge clk) $past(add2(1)) == 3);
  // Unlike other side effects, also with a draw beneath them
  int fd = 0;
  assert property (@(posedge clk) $past($fgetc(fd ^ int'($urandom & 0))) != -2);
  assert property (@(posedge clk) $past(capture()) >= 0);
  assert property (@(posedge clk) $rose(capture() > 3) |-> 1);

  // A match item value with side effects is evaluated each clock, not on each match, or not at
  // all if unused, against IEEE 1800-2023 16.10
  int calls = 0;
  function automatic int capture();
    ++calls;
    return calls;
  endfunction
  int used_fails = 0;
  property p_used;
    int snap;
    @(posedge clk) (cyc == 3, snap = capture()) |=> snap == 0;
  endproperty
  assert property (p_used)
  else ++used_fails;
  property p_unused;
    int snap;
    @(posedge clk) (cyc == 5, snap = capture()) |=> 1;
  endproperty
  assert property (p_unused);
  // Each part with side effects warns
  property p_parts;
    int snap;
    @(posedge clk) (cyc == 7, snap = capture()
    /* verilator lint_off SIDEEFFECT */
    +
    /* verilator lint_on SIDEEFFECT */
    capture()) |=> snap != 0;
  endproperty
  int parts_fails = 0;
  assert property (p_parts)
  else ++parts_fails;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    a <= cyc[0];
    if (cyc == 99) begin
      // The match of p_used fails, and p_parts passes, each capture() call returning above 0
      `checkd(used_fails, 1);
      `checkd(parts_fails, 0);
      `checkd(calls >= 3, 1'b1);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
