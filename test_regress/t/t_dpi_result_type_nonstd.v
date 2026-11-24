// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// DPI functions with a non-standard result type, which C takes as the first argument

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t;
  // verilator lint_off NONSTD
  import "DPI-C" function bit [32:0] i_bit33(input bit [32:0] in);
  import "DPI-C" function bit [127:0] i_bit128(input bit [127:0] in);
  import "DPI-C" function logic [1:0] i_logic2(input logic [1:0] in);
  import "DPI-C" function logic [99:0] i_logic100(input logic [99:0] in);
  export "DPI-C" function e_bit65;
  export "DPI-C" function e_logic56;
  function bit [64:0] e_bit65(input bit [64:0] in);
    return ~in;
  endfunction
  function logic [55:0] e_logic56(input logic [55:0] in);
    return in;
  endfunction
  // verilator lint_on NONSTD
  import "DPI-C" context function int check_exports();

  initial begin
    `checkh(i_bit33(33'h1_2345_6789), 33'h0_dcba_9876);
    `checkh(i_bit128(128'h0123_4567_89ab_cdef_fedc_ba98_7654_3210),
            128'hfedc_ba98_7654_3210_0123_4567_89ab_cdef);
    `checkh(i_logic2(2'b10), 2'b01);
    `checkh(i_logic100(100'h9_0123_4567_89ab_cdef_0123_4567),
            100'h9_0123_4567_89ab_cdef_0123_4567);
    `checkh(check_exports(), 0);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
