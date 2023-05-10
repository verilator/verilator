// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

function bit check_string(string s);
  if (s inside {"RW", "WO"})
    return 1'b1;
  return 1'b0;
endfunction

function bit check_double(real d);
  if (d inside {0.0, 2.5})
    return 1'b1;
  return 1'b0;
endfunction

module t();
  initial begin
    if (!check_string("WO"))
      $stop;
    if (!check_string("RW"))
      $stop;
    if (check_string("ABC"))
      $stop;
    if (!check_double(0.0))
      $stop;
    if (!check_double(2.5))
      $stop;
    if (check_double(1.0))
      $stop;

    $display("*-* All Finished *-*");
    $finish;
  end
endmodule
