// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

  string s;

  initial begin
    for (int a = 0; a < 3; ++a) begin : a_loop
      s += $sformatf(" a%0d", a);  // <--- Error: += is not legal on strings
      s = s + s;  // <--- Error: += is not legal on strings
    end

    $stop;
  end

endmodule
