// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkb(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='b%x exp='b%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

module t;
  // `IEEE1800-2023 7.3.1 Packed unions` says:
  // If a packed union contains a 2-state member and a 4-state member, the entire union is 4-state. There is an
  // implicit conversion from 4-state to 2-state when reading and from 2-state to 4-state when writing the 2-state
  // member.
  typedef union packed {
    bit b;
    logic l;
  } union_t;
  typedef union_t union_array_t[1];

  function automatic union_t make_value_b();
    union_t value;
    // Standard says that "There is an implicit conversion" not that it may be an implicit conversion
    // therefore this actually is:
    //  value = logic'(bit'(1'bx))
    //  ^~~~~   ^~~~~~ ^~~~
    //  union   |      this conversion happens because we are assigning to the two-state bit `b`
    //          this conversion is required by the IEEE
    value.b = 1'bx;
    return value;
  endfunction

  function automatic union_t make_value_l();
    union_t value;
    value.l = 1'bx;
    return value;
  endfunction

  function automatic bit check_ambiguous_cond(input logic cond);
    union_array_t lhs = '{union_t'(1'b1)};
    union_array_t rhs = '{union_t'(1'b0)};
    return (cond ? lhs : rhs) === union_array_t'{union_t'(1'bx)};
  endfunction

  localparam union_t VALUE_B = make_value_b();
  localparam union_t VALUE_L = make_value_l();
  localparam bit COND_X = check_ambiguous_cond(1'bx);
  localparam bit COND_Z = check_ambiguous_cond(1'bz);

  initial begin
    `checkb(VALUE_B.b, 1'b0);
    `checkb(VALUE_B.l, 1'b0);
    `checkb(VALUE_L.b, 1'b0);
    `checkb(VALUE_L.l, 1'bx);
    `checkb(COND_X, 1'b1);
    `checkb(COND_Z, 1'b1);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
