// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: Copyright 2026 Google LLC
// SPDX-License-Identifier: CC0-1.0

class C;
  rand byte data[];
  rand int size_val;

  constraint c_size {
    size_val == 20;
    data.size() == size_val;
  }

  constraint c_data {
    foreach (data[i]) {
      // Pick values in two disconnected ranges
      data[i] dist { [0:10] := 1, [100:110] := 1 };
      // Inter-element constraint: sorted
      if (i > 0) data[i] > data[i-1];
    }
  }
endclass

module t;
  initial begin
    static C c = new;
    if (c.randomize() == 0) begin
      $display("%%Error: Randomization failed");
      $stop;
    end

    // Check results
    foreach (c.data[i]) begin
      if (!((c.data[i] >= 0 && c.data[i] <= 10) || (c.data[i] >= 100 && c.data[i] <= 110))) begin
        $display("%%Error: Element %0d out of range: %0d", i, c.data[i]);
        $stop;
      end
      if (i > 0 && c.data[i] <= c.data[i-1]) begin
        $display("%%Error: Elements %0d and %0d not sorted: %0d, %0d", i-1, i, c.data[i-1], c.data[i]);
        $stop;
      end
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
