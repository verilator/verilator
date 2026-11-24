// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// DPI functions with a non-standard result type, which C takes as the first argument

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t;
  typedef bit bit_t;
  typedef bit [94:0] bit95_t;
  typedef logic [64:0] logic65_t;
  typedef struct packed {
    bit [15:0] x;
    bit [16:0] y;
  } struct_2_state_33_t;
  typedef struct packed {
    logic [3:0] x;
    bit [4:0] y;
  } struct_4_state_9_t;
  typedef union packed {
    bit [64:0] x;
    bit [64:0] y;
  } union_2_state_65_t;
  typedef union packed {
    logic [16:0] x;
    bit [16:0] y;
  } union_4_state_17_t;

  // Warns NONSTD
  import "DPI-C" function bit [32:0] i_bit33(input bit [32:0] in);
  export "DPI-C" function e_logic56;
  function logic [55:0] e_logic56(input logic [55:0] in);
    return in;
  endfunction

  // verilator lint_off NONSTD
  import "DPI-C" function bit [127:0] i_bit128(input bit [127:0] in);
  // verilator lint_off ASCRANGE
  import "DPI-C" function bit [1:33] i_bit_1_33(input bit [1:33] in);
  // verilator lint_on ASCRANGE
  import "DPI-C" function bit_t [32:0] i_bit_t_33(input bit_t [32:0] in);
  import "DPI-C" function struct_2_state_33_t i_struct_2_state_33(input struct_2_state_33_t in);
  import "DPI-C" function logic [1:0] i_logic2(input logic [1:0] in);
  import "DPI-C" function logic [99:0] i_logic100_xz(input logic [99:0] in);
  import "DPI-C" function logic65_t i_logic65_t(input logic65_t in);
  import "DPI-C" function integer i_integer(input int in);
  import "DPI-C" function union_4_state_17_t i_union_4_state_17(input union_4_state_17_t in);

  export "DPI-C" function e_bit65;
  function bit [64:0] e_bit65(input bit [64:0] in);
    return ~in;
  endfunction
  export "DPI-C" function e_bit95_t;
  function bit95_t e_bit95_t(input bit95_t in);
    return ~in;
  endfunction
  export "DPI-C" function e_union_2_state_65;
  function union_2_state_65_t e_union_2_state_65(input union_2_state_65_t in);
    return union_2_state_65_t'(in.x + 1);
  endfunction
  export "DPI-C" function e_logic_8_2;
  function logic [8:2] e_logic_8_2(input logic [8:2] in);
    return ~in;
  endfunction
  export "DPI-C" function e_integer;
  function integer e_integer(input int in);
    return in + 1;
  endfunction
  export "DPI-C" function e_struct_4_state_9;
  function struct_4_state_9_t e_struct_4_state_9(input struct_4_state_9_t in);
    return '{x: in.y[3:0], y: {in.y[4], in.x}};
  endfunction
  // verilator lint_on NONSTD

  import "DPI-C" context function int check_exports();

  initial begin
    `checkh(i_bit33(33'h1_2345_6789), 33'h0_dcba_9876);
    `checkh(i_bit128(128'h0123_4567_89ab_cdef_fedc_ba98_7654_3210),
            128'hfedc_ba98_7654_3210_0123_4567_89ab_cdef);
    `checkh(i_bit_1_33(33'h0_ffff_ffff), 33'h1_0000_0000);
    `checkh(i_bit_t_33(33'h0_8000_0001), 33'h1_0000_0002);
    `checkh(i_struct_2_state_33(struct_2_state_33_t'{x: 16'h1234, y: 17'h1_5678}),
            {16'h0, 17'h1_5678});
    `checkh(i_logic2(2'b10), 2'b01);
    `checkh(i_logic100_xz(100'h9_0123_4567_89ab_cdef_0123_4567),
            100'h9_0123_4567_89ab_cdef_0123_4567);
    `checkh(i_logic65_t(65'h1_0123_4567_89ab_cdef), 65'h0_fedc_ba98_7654_3210);
    `checkh(i_integer(21), 42);
    `checkh(i_union_4_state_17(union_4_state_17_t'(17'h1_0001)), 17'h0_0003);
    `checkh(check_exports(), 0);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
