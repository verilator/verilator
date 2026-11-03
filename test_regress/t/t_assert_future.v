// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  global clocking @(posedge clk);
  endclocking

  logic a;
  bit [6:0] values[2];
  bit [6:0] matrix[2][3];

  //PASSES:
  int count_not_stable;  // Counts changes
  assert property (@(posedge clk) $stable(a))
  else count_not_stable = count_not_stable + 1;

  int count_not_stable_gclk;  // Counts changes
  assert property (@(posedge clk) $stable_gclk(a))
  else count_not_stable_gclk = count_not_stable_gclk + 1;

  int count_changing_gclk;
  assert property (@(posedge clk) $changing_gclk(a)) count_changing_gclk = count_changing_gclk + 1;

  int count_falling_gclk;
  assert property (@(posedge clk) $falling_gclk(a)) count_falling_gclk = count_falling_gclk + 1;

  int count_future_gclk;  // Counts changes
  assert property (@(posedge clk) $future_gclk(a) != a) count_future_gclk = count_future_gclk + 1;

  int count_rising_gclk;
  assert property (@(posedge clk) $rising_gclk(a)) count_rising_gclk = count_rising_gclk + 1;

  int count_not_steady_gclk;  // Counts changes
  assert property (@(posedge clk) $steady_gclk(a))
  else count_not_steady_gclk = count_not_steady_gclk + 1;

  int count_array_changes;
  assert property (@(posedge clk) $changing_gclk(values))
    count_array_changes = count_array_changes + 1;

  int count_array_not_steady;
  assert property (@(posedge clk) $steady_gclk(values))
  else count_array_not_steady = count_array_not_steady + 1;

  int count_array_future;
  assert property (@(posedge clk) $future_gclk(values) != values)
    count_array_future = count_array_future + 1;

  property array_samples(signal);
    $steady_gclk(signal) == !$changing_gclk(signal)
    && $steady_gclk(signal) == ($future_gclk(signal) == signal);
  endproperty
  assert property (@(posedge clk) array_samples(matrix))
  else `stop;
  assert property (@(posedge clk) array_samples(matrix[0]))
  else `stop;
  assert property (@(posedge clk) array_samples(matrix[0][1:2]))
  else `stop;
  assert property (@(posedge clk) array_samples(values[1]))
  else `stop;

  int cyc = 0;

  always @(posedge clk) begin
`ifdef TEST_VERBOSE
    $display("[%0t] cyc=%0d a=%0x gs=%x gsc=%x", $time, cyc, a, count_not_stable,
             count_not_stable_gclk);
`endif
    cyc <= cyc + 1;
    if (cyc <= 3) begin
      a <= 0;
      count_not_stable = 0;
      count_not_stable_gclk = 0;
    end
    else if (cyc == 4) begin
      a <= 0;  // stable
    end
    else if (cyc == 5) begin
      a <= 1;  // rise
      values[1] <= 7'h40;
      matrix[0][2] <= 7'h40;
    end
    else if (cyc == 6) begin
      a <= 1;  // stable
    end
    else if (cyc == 7) begin
      a <= 0;  // fall
      values[1] <= 0;
      matrix[0][2] <= 0;
    end
    else if (cyc == 10) begin
      `checkd(count_not_stable, 2);
      `checkd(count_not_stable_gclk, 2);
      `checkd(count_changing_gclk, 2);
      `checkd(count_falling_gclk, 1);
      `checkd(count_future_gclk, 2);
      `checkd(count_rising_gclk, 1);
      `checkd(count_not_steady_gclk, 2);
      `checkd(count_array_changes, 2);
      `checkd(count_array_not_steady, 2);
      `checkd(count_array_future, 2);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
