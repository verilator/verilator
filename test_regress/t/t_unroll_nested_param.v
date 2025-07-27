// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

  int a, b;
  int pos;

  function string value;
    // Debug 'initial' loops first
    value = "";
    for (int exit_a = 0; exit_a < 2; ++exit_a) begin
      for (int exit_b = 0; exit_b < 3; ++exit_b) begin
        b = 0;
        value = {value, $sformatf("exit_a %0d %0d", exit_a, exit_b)};
        for (a = 0; a < 3; ++a) begin : a_loop
          value = {value, $sformatf("  A%0d", a * 10 + b)};
          for (b = 0; b < 3; ++b) begin : b_loop
            value = {value, $sformatf(" B%0d", a * 10 + b)};
            if (exit_b == 1 && b == 1) disable b_loop;
            value = {value, $sformatf(" C%0d", a * 10 + b)};
            if (exit_b == 2 && a == 1) disable a_loop;
            value = {value, $sformatf(" D%0d", a * 10 + b)};
          end
          value = {value, $sformatf("  Y%0d", a * 10 + b)};
          if (exit_a == 1 && a == 1) disable a_loop;
          value = {value, $sformatf("  Z%0d", a * 10 + b)};
        end
        value = {value, "\n"};
      end
    end
  endfunction

  localparam string VALUE = value();

  initial begin
    $write("%s", VALUE);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
