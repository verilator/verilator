// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

`ifdef VERILATOR
`define IMPURE_ONE ($c(1))
`else
`define IMPURE_ONE (|($random | $random))
`endif

module t;
  static int calls = 0;

  function logic f(logic a);
    if (a === 1'b1) $write("1");
    else if (a === 1'b0) $write("0");
    else if (a === 1'bx) $write("x");
    else if (a === 1'bz) $write("z");
    else $stop;
    $write("\n");
    return a;
  endfunction

  function integer f2(integer a);
    return a;
  endfunction

  function logic bar();
    calls++;
    return 'x;
  endfunction

  initial begin
    static integer result;
    if ((f(0) ? f(1) : f(0)) !== 0) $stop;
    if ((f(1) ? f(1) : f(0)) !== 1) $stop;
    if ((f('x) ? f(1) : f(0)) !== 'x) $stop;
    if ((f('x) ? f(1) : f(1)) !== 1) $stop;
    if ((f('z) ? f(1) : f(0)) !== 'x) $stop;
    if ((f('z) ? f(0) : f(0)) !== 0) $stop;
    if ((`IMPURE_ONE ? 0 : bar()) !== 0) $stop;
    if (calls !== 0) $stop;

    if ((f(1) ? f2(32'h1fx1) : f2('x)) !== 32'h1fx1) $stop;
    if ((f(0) ? f2(123) : f2(432)) !== 432) $stop;
    if ((
      f('x) ?
       f2(32'b01011001011110101010100101000111) :
       f2(32'b01011001011110101010100101000111)
    ) !== 32'b01011001011110101010100101000111) $stop;
    if ((
      f('z) ?
       f2(32'b01011001001010101010100101000111) :
       f2(32'b01011001010110101010100101000111)
    ) !== 32'b010110010xxx10101010100101000111) $stop;
    if ((
      f('x) ?
       f2(32'bz101100101111xx0101x1z0x010001x1) :
       f2(32'b0101100zz1111010011z1z0x01000111)
    ) !== 32'bx101100xx1111xx0xx1x1x0x010001x1) $stop;

    if ((1 ? f2(32'h1fx1) : f2('x)) !== 32'h1fx1) $stop;
    if ((0 ? f2(123) : f2(432)) !== 432) $stop;
    if ((
      'x ?
       f2(32'b01011001011110101010100101000111) :
       f2(32'b01011001011110101010100101000111)
    ) !== 32'b01011001011110101010100101000111) $stop;
    if ((
      'z ?
       f2(32'b01011001001010101010100101000111) :
       f2(32'b01011001010110101010100101000111)
    ) !== 32'b010110010xxx10101010100101000111) $stop;
    result = 'x ?
       f2(32'bz101100101111xx0101x1z0x010001x1) :
       f2(32'b0101100zz1111010011z1z0x01000111);
    if (result !== 32'bx101100xx1111xx0xx1x1x0x010001x1) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
