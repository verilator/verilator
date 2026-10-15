// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t(
  total
);

  output total;  // Output, so doesn't get removed
  int total = 0;

  logic clk = 0;
  always #5 clk = ~clk;

  int cyc = 0;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 5) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  // That's right. 70k. Clang has a secret 64k maximum limit on
  // member constructor calls, above which it silently not runs them
  localparam int N = 70000;

  // Only touch the strings in 'initial' and 'final', which are slow code,
  // otherwise the generated C++ takes very long to compile. Also don't
  // check any intermediate result for the same reason.
  for (genvar i = 0; i < N; ++i) begin : gen
    // Strings are not trivially constructible, so this module will need
    // to initialize ~N member variables when constructed at runtime.
    string s;
    initial s = $sformatf("%0d", $time);
    final total += s.len();
  end

endmodule
