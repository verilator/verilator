// DESCRIPTION: Verilator: Verilog Test module
//
// A class specialization whose parameter's type depends on a parameter given
// after it, or on a type parameter, is named from every pin's folded value,
// so specializations with equal values are one class, and others are not.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Michael Bedford Taylor
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// P's width comes from N
class clw #(
    parameter int N = 1,
    // verilator lint_off WIDTHTRUNC
    parameter logic [N-1:0] P = '0  // Given wider values
    // verilator lint_on WIDTHTRUNC
);
  static int count;
  static function int value();
    return int'(P);
  endfunction
endclass

// P and Q have type T
class clt #(
    parameter type T = byte,
    // verilator lint_off WIDTHTRUNC
    parameter T P = 0,  // Given wider values
    parameter T Q = 0
    // verilator lint_on WIDTHTRUNC
);
  static int count;
  static function int value();
    return int'(Q);
  endfunction
endclass

module t;
  localparam int TWO = 2;
  logic [3:0] tv;

  typedef clw#(.P(8'h81), .N(TWO * 4)) clw81_t;  // Width given after the value
  typedef clw#(.P(8'h01), .N(TWO * 4)) clw01_t;  // Differs from clw81_t only above bit 0
  typedef clw#(.P(8'h81), .N(TWO * 2)) clw4a_t;  // Equal to clw4b_t once P is 4 bits
  typedef clw#(.P(8'h01), .N(TWO * 2)) clw4b_t;
  clw4a_t clw4a;
  clw4b_t clw4b;

  typedef clt#(.P(8'h01), .T(type(tv)), .Q(8'h81)) clta_t;  // Equal to cltb_t once T is known
  typedef clt#(.P(8'h01), .T(type(tv)), .Q(8'h01)) cltb_t;
  typedef clt#(.P(8'h02), .T(type(tv)), .Q(8'h01)) cltc_t;  // The same, in the other order
  typedef clt#(.P(8'h02), .T(type(tv)), .Q(8'h81)) cltd_t;
  typedef clt#(.T(type(tv)), .P(8'h03), .Q(8'h81)) clte_t;  // The same, with T given first
  typedef clt#(.T(type(tv)), .P(8'h03), .Q(8'h01)) cltf_t;
  clta_t clta;
  cltb_t cltb;

  initial begin
    `checkh(clw81_t::value(), 'h81);
    `checkh(clw01_t::value(), 'h01);
    clw4a = new;
    clw4b = clw4a;  // One specialization, so one type
    clw4a_t::count = 7;
    `checkd(clw4b_t::count, 7);
    `checkh(clw4b_t::value(), 'h1);

    clta = new;
    cltb = clta;  // One specialization, so one type
    clta_t::count = 1;
    cltc_t::count = 2;
    clte_t::count = 3;
    `checkd(cltb_t::count, 1);
    `checkd(cltd_t::count, 2);
    `checkd(cltf_t::count, 3);
    `checkh(cltb_t::value(), 'h1);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
