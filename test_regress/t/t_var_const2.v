// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  const static int a1;
  const static int a2 = 0;

  initial begin
    const static int c1;
    const static int c2 = 0;

    const automatic int d1;
    const automatic int d2 = 0;
  end

  function static void tb_func1();
    const static int e1;
    const static int e2 = 0;

    const automatic int f1;
    const automatic int f2 = 0;
  endfunction

  function automatic void tb_func2();
    const static int g1;
    const static int g2 = 0;

    const automatic int h1;
    const automatic int h2 = 0;
  endfunction
endmodule
