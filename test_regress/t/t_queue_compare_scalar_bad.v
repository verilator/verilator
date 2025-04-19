// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Shou-Li Hsu.
// SPDX-License-Identifier: CC0-1.0

module t;
  initial begin
    // Create a queue
    int queue_var[$] = '{1, 2, 3};

    // This should fail: comparing queue to scalar
    if (queue_var == 1) begin
      $display("Queue equals 1");
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
