// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2022 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

  typedef enum {
    ZERO,
    ONE,
    TWO
  } e_t;

  typedef enum {
    THREE = 3,
    FOUR,
    FIVE
  } o_t;

  typedef struct packed {
    e_t m_e;
    o_t m_o;
  } struct_t;

  function automatic void output_int(output int status);
  endfunction

  function automatic void inout_int(inout int status);
  endfunction

  function automatic void ref_int(ref int status);
  endfunction

  function automatic void input_enum(input e_t status);
  endfunction

  function automatic void inout_enum(inout e_t status);
  endfunction

  function automatic void ref_enum(ref e_t status);
  endfunction

  initial begin
    e_t e;
    o_t o;
    struct_t str;
    int enum_int;

    e = ONE;
    e = $random() == 0 ? ONE : TWO;
    e = e_t'(1);
    e = e;

    e = 1;  // Bad
    o = e;  // Bad

    str.m_e = ONE;
    str.m_o = THREE;
    e = str.m_e;
    o = str.m_o;
    o = str.m_e;  // Bad

    o = e_t'(1);  // Bad

    e = e + 1;  // Bad
    e = int'(e);  // Bad
    e = (e == ONE);  // Bad
    o = e + 1;  // Bad
    e = o_t'(e);  // Bad
    e = e_t'(1) + 1;  // Bad
    o = e_t'(o_t'(e));  // Bad
    e = int'(o_t'(e));  // Bad

    output_int(e);
    inout_int(e);
    ref_int(e);

    input_enum(enum_int);
    inout_enum(enum_int);
    ref_enum(enum_int);
  end
endmodule
