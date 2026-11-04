// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv, expv) \
  do if ((gotv) !== (expv)) begin \
    $write("%%Error: %s:%0d: got='h%x exp='h%x\n", `__FILE__, `__LINE__, (gotv), (expv)); \
    `stop; \
  end while (0)

class ParamXClass;
endclass

module sub #(
    parameter logic [1:0] P = 2'bx0
) (
    output logic is_x,
    output logic is_z
);
  assign is_x = P === 2'bx0;
  assign is_z = P === 2'bz0;
endmodule

module t;
  typedef logic [3:0] array_t[2];
  typedef bit [6:0] bit_vec_t;
  typedef bit [2:0][4:0] packed_bit_array_t;
  typedef logic [2:0][4:0] packed_logic_array_t;
  /* verilator lint_off ASCRANGE */
  typedef logic [4:0] ascending_array_t[1:3];
  /* verilator lint_on ASCRANGE */
  typedef bit [3:0] bit_array_t[2];
  typedef logic [3:0] logic_array_t[2];
  typedef logic [4:0] descending_array_t[3:1];
  typedef logic [2:0] nested_row_t[2];
  typedef nested_row_t nested_array_t[2];
  typedef real real_array_t[2];
  typedef struct packed {
    logic [3:0] first;
    logic [2:0] second;
  } packed_struct_t;
  typedef struct packed {
    bit [3:0] first;
    logic [2:0] second;
  } mixed_packed_struct_t;
  typedef struct packed {
    bit [2:0] first;
    bit second;
  } packed_2state_struct_t;
  typedef struct packed {
    logic [2:0] first;
    logic second;
  } packed_4state_struct_t;
  typedef struct packed {
    packed_2state_struct_t first;
    bit [1:0] second;
  } packed_nested_2state_struct_t;
  typedef struct packed {
    packed_2state_struct_t first;
    logic [1:0] second;
  } packed_nested_mixed_struct_t;
  typedef struct packed {
    packed_4state_struct_t first;
    bit [1:0] second;
  } packed_nested_4state_struct_t;
  typedef packed_2state_struct_t packed_2state_struct_array_t[1];
  typedef packed_4state_struct_t packed_4state_struct_array_t[1];
  typedef mixed_packed_struct_t mixed_packed_struct_array_t[1];
  typedef packed_nested_2state_struct_t packed_nested_2state_struct_array_t[1];
  typedef packed_nested_mixed_struct_t packed_nested_mixed_struct_array_t[1];
  typedef packed_nested_4state_struct_t packed_nested_4state_struct_array_t[1];
  typedef struct {
    bit [3:0] first;
    logic [2:0] second;
  } unpacked_struct_t;
  typedef string string_array_t[2];

  logic default_is_x;
  logic default_is_z;
  logic explicit_is_x;
  logic explicit_is_z;
  logic x_is_x;
  logic x_is_z;
  logic z_is_x;
  logic z_is_z;

  sub sub_default (default_is_x, default_is_z);
  sub #(.P(2'bx0)) sub_explicit (explicit_is_x, explicit_is_z);
  sub #(.P(2'bx0)) sub_x (x_is_x, x_is_z);
  sub #(.P(2'bz0)) sub_z (z_is_x, z_is_z);

  function automatic logic eval_and(input logic lhs, input logic rhs);
    return lhs && rhs;
  endfunction

  function automatic bit_vec_t eval_bit_cast(input logic [6:0] value);
    return bit_vec_t'(value);
  endfunction

  function automatic bit_vec_t eval_bit_assign(input logic [6:0] value);
    bit_vec_t result = value;
    return result;
  endfunction

  function automatic logic eval_or(input logic lhs, input logic rhs);
    return lhs || rhs;
  endfunction

  function automatic logic eval_if(input logic lhs, input logic rhs);
    return lhs -> rhs;
  endfunction

  /* verilator lint_off WIDTHTRUNC */
  function automatic logic eval_and_wide(input logic [1:0] lhs, input logic [1:0] rhs);
    return lhs && rhs;
  endfunction

  function automatic logic eval_or_wide(input logic [1:0] lhs, input logic [1:0] rhs);
    return lhs || rhs;
  endfunction

  function automatic logic eval_if_wide(input logic [1:0] lhs, input logic [1:0] rhs);
    return lhs -> rhs;
  endfunction

  function automatic bit eval_if_stmt(input logic [1:0] cond);
    if (cond) return 1'b1;
    else return 1'b0;
  endfunction

  function automatic int eval_while(input logic [1:0] cond);
    eval_while = 0;
    while (cond) begin
      ++eval_while;
      cond = 2'b00;
    end
  endfunction

  function automatic int eval_do_while(input logic cond);
    eval_do_while = 0;
    do begin
      ++eval_do_while;
      if (cond === 1'b1) cond = 1'b0;
    end while (cond);
  endfunction

  function automatic int eval_for(input logic [1:0] cond);
    eval_for = 0;
    for (; cond; cond = 2'b00) ++eval_for;
  endfunction

  function automatic int eval_repeat(input logic [31:0] count);
    eval_repeat = 0;
    repeat (count) ++eval_repeat;
  endfunction
  /* verilator lint_on WIDTHTRUNC */

  /* verilator lint_off CASEWITHX */
  function automatic int eval_case(input logic [2:0] value);
    case (value)
      3'b0x1: eval_case = 1;
      3'b0z1: eval_case = 2;
      3'b001: eval_case = 3;
      default: eval_case = 4;
    endcase
  endfunction

  function automatic int eval_casez(input logic [2:0] value);
    casez (value)
      3'b110: eval_casez = 1;
      3'b1?1: eval_casez = 2;
      3'b1x0: eval_casez = 3;
      default: eval_casez = 4;
    endcase
  endfunction

  /* verilator lint_off CASEX */
  function automatic int eval_casex(input logic [2:0] value);
    casex (value)
      3'b110: eval_casex = 1;
      3'b0x1: eval_casex = 2;
      3'b0z0: eval_casex = 3;
      default: eval_casex = 4;
    endcase
  endfunction
  /* verilator lint_on CASEX */

  function automatic int eval_case_inside(input logic [2:0] value);
    case (value) inside
      3'b1x0: eval_case_inside = 1;
      3'b0z1: eval_case_inside = 2;
      default: eval_case_inside = 3;
    endcase
  endfunction

  function automatic int eval_case_inside_range(input logic [31:0] value);
    case (value) inside
      [32'd2:32'd4]: eval_case_inside_range = 1;
      [$:32'd1]: eval_case_inside_range = 2;
      [32'd5:$]: eval_case_inside_range = 3;
      default: eval_case_inside_range = 4;
    endcase
  endfunction

  function automatic int eval_case_inside_range_narrow(input logic [14:0] value);
    case (value) inside
      [15'd17:15'd29]: eval_case_inside_range_narrow = 1;
      default: eval_case_inside_range_narrow = 2;
    endcase
  endfunction

  function automatic int eval_case_inside_range_signed(input int signed value);
    case (value) inside
      [-3:-1]: eval_case_inside_range_signed = 1;
      default: eval_case_inside_range_signed = 2;
    endcase
  endfunction

  function automatic int eval_case_inside_range_real(input real value);
    case (value) inside
      [1.5:3.0]: eval_case_inside_range_real = 1;
      default: eval_case_inside_range_real = 2;
    endcase
  endfunction

  /* verilator lint_on CASEWITHX */

  function automatic logic [6:0] eval_cond(input logic cond, input logic [6:0] lhs,
                                            input logic [6:0] rhs);
    return cond ? lhs : rhs;
  endfunction

  function automatic logic [32:0] eval_cond_wide(input logic cond, input logic [32:0] lhs,
                                                  input logic [32:0] rhs);
    return cond ? lhs : rhs;
  endfunction

  function automatic string eval_string(input logic cond);
    return cond ? "then" : "else";
  endfunction

  function automatic real eval_real(input logic cond);
    return cond ? 1.25 : 2.5;
  endfunction

  function automatic string eval_string_values(input logic cond, input string lhs,
                                                 input string rhs);
    return cond ? lhs : rhs;
  endfunction

  function automatic real eval_real_values(input logic cond, input real lhs, input real rhs);
    return cond ? lhs : rhs;
  endfunction

  function automatic string eval_string_variables(input logic cond);
    string lhs = "then";
    string rhs = "else";
    return cond ? lhs : rhs;
  endfunction

  function automatic real eval_real_variables(input logic cond);
    real lhs = 1.25;
    real rhs = 2.5;
    return cond ? lhs : rhs;
  endfunction

  function automatic array_t eval_array(input logic cond, input array_t lhs, input array_t rhs);
    return cond ? lhs : rhs;
  endfunction

  function automatic packed_struct_t eval_packed_struct(input logic cond,
                                                         input packed_struct_t lhs,
                                                         input packed_struct_t rhs);
    return cond ? lhs : rhs;
  endfunction

  function automatic bit eval_packed_2state_struct_default(input logic cond);
    packed_2state_struct_array_t lhs = '{packed_2state_struct_t'(4'b1011)};
    packed_2state_struct_array_t rhs = '{packed_2state_struct_t'(4'b0100)};
    return (cond ? lhs : rhs)
           === packed_2state_struct_array_t'{packed_2state_struct_t'(4'b0000)};
  endfunction

  function automatic bit eval_packed_bit_array_default();
    packed_bit_array_t value;
    return value === '0;
  endfunction

  function automatic bit eval_packed_logic_array_default();
    packed_logic_array_t value;
    return $isunknown(value);
  endfunction

  function automatic bit eval_packed_4state_struct_default(input logic cond);
    packed_4state_struct_array_t lhs = '{packed_4state_struct_t'(4'b1011)};
    packed_4state_struct_array_t rhs = '{packed_4state_struct_t'(4'b0100)};
    return (cond ? lhs : rhs)
           === packed_4state_struct_array_t'{packed_4state_struct_t'(4'bxxxx)};
  endfunction

  function automatic bit eval_mixed_packed_struct_default(input logic cond);
    mixed_packed_struct_array_t lhs = '{mixed_packed_struct_t'(7'b1011_001)};
    mixed_packed_struct_array_t rhs = '{mixed_packed_struct_t'(7'b0100_110)};
    return (cond ? lhs : rhs)
           === mixed_packed_struct_array_t'{mixed_packed_struct_t'(7'bxxxx_xxx)};
  endfunction

  function automatic bit eval_packed_nested_2state_struct_default(input logic cond);
    packed_nested_2state_struct_array_t lhs
        = '{packed_nested_2state_struct_t'(6'b1011_01)};
    packed_nested_2state_struct_array_t rhs
        = '{packed_nested_2state_struct_t'(6'b0100_10)};
    return (cond ? lhs : rhs)
           === packed_nested_2state_struct_array_t'{packed_nested_2state_struct_t'(6'b000000)};
  endfunction

  function automatic bit eval_packed_nested_mixed_struct_default(input logic cond);
    packed_nested_mixed_struct_array_t lhs
        = '{packed_nested_mixed_struct_t'(6'b1011_01)};
    packed_nested_mixed_struct_array_t rhs
        = '{packed_nested_mixed_struct_t'(6'b0100_10)};
    return (cond ? lhs : rhs)
           === packed_nested_mixed_struct_array_t'{packed_nested_mixed_struct_t'(6'bxxxxxx)};
  endfunction

  function automatic bit eval_packed_nested_4state_struct_default(input logic cond);
    packed_nested_4state_struct_array_t lhs
        = '{packed_nested_4state_struct_t'(6'b1011_01)};
    packed_nested_4state_struct_array_t rhs
        = '{packed_nested_4state_struct_t'(6'b0100_10)};
    return (cond ? lhs : rhs)
           === packed_nested_4state_struct_array_t'{packed_nested_4state_struct_t'(6'bxxxxxx)};
  endfunction

  function automatic bit eval_array_ok(input logic cond, input array_t lhs, input array_t rhs);
    array_t result = eval_array(cond, lhs, rhs);
    return result[0] === 4'bxxxx && result[1] === 4'bxxxx;
  endfunction

  function automatic bit eval_nested_array_ok(input logic cond, input nested_array_t lhs,
                                               input nested_array_t rhs);
    nested_array_t result = cond ? lhs : rhs;
    return result[0][0] === 3'bxxx && result[0][1] === 3'bxxx
           && result[1][0] === 3'bxxx && result[1][1] === 3'bxxx;
  endfunction

  function automatic bit eval_string_array_ok(input logic cond, input string_array_t lhs,
                                               input string_array_t rhs);
    string_array_t result = cond ? lhs : rhs;
    return result[0] == "same" && result[1] == "";
  endfunction

  function automatic logic eval_packed_select(input logic [1:0] index);
    logic [3:0] value = 4'b1010;
    return value[index];
  endfunction

  function automatic logic [3:0] eval_packed_write(input logic [1:0] index);
    logic [3:0] value = 4'b1010;
    value[index] = 1'b1;
    return value;
  endfunction

  function automatic logic [1:0] eval_packed_part_select(input logic [1:0] index);
    logic [3:0] value = 4'b1010;
    return value[index +: 2];
  endfunction

  function automatic logic [3:0] eval_packed_part_write(input logic [1:0] index);
    logic [3:0] value = 4'b1010;
    value[index +: 2] = 2'b11;
    return value;
  endfunction

  function automatic logic [3:0] eval_array_select(input logic index, input array_t value);
    return value[index];
  endfunction

  function automatic bit eval_array_write_ok(input logic index, input array_t value);
    array_t original = value;
    value[index] = 4'b1111;
    return value[0] === original[0] && value[1] === original[1];
  endfunction

  function automatic bit eval_bit_array_select_ok(input logic index, input bit_array_t value);
    return value[index] == 4'b0000;
  endfunction

  function automatic bit eval_bit_array_write_ok(input logic [3:0] rhs,
                                                   input bit_array_t value);
    value[0] = rhs;
    return value[0] === 4'b0000;
  endfunction

  function automatic bit eval_bit_array_assign_ok();
    bit_array_t value;
    value = '{4'bxxxx, 4'bzzzz};
    return value[0] === 4'b0000 && value[1] === 4'b0000;
  endfunction

  function automatic logic_array_t eval_logic_array(input logic [3:0] first,
                                                     input logic [3:0] second);
    logic_array_t value;
    value[0] = first;
    value[1] = second;
    return value;
  endfunction

  function automatic bit eval_unpacked_struct_assign_ok();
    unpacked_struct_t value;
    value = '{4'bxxxx, 3'bx01};
    return value.first === 4'b0000 && value.second === 3'bx01;
  endfunction

  function automatic unpacked_struct_t eval_unpacked_struct_cond_default(input logic cond);
    return cond ? unpacked_struct_t'{4'b1011, 3'b001}
                : unpacked_struct_t'{4'b1001, 3'b011};
  endfunction

  function automatic unpacked_struct_t eval_unpacked_struct_cond_same(input logic cond);
    return cond ? unpacked_struct_t'{4'b1011, 3'b001}
                : unpacked_struct_t'{4'b1011, 3'b001};
  endfunction

  function automatic ParamXClass eval_class_cond_same(input logic cond);
    return cond ? null : null;
  endfunction

  function automatic bit eval_mixed_packed_struct_assign_ok();
    mixed_packed_struct_t value;
    value = 7'bxxxx_x01;
    return value === 7'bxxxx_x01 && value.first === 4'b0000 && value.second === 3'bx01;
  endfunction

  function automatic bit eval_mixed_packed_struct_read_ok();
    mixed_packed_struct_t value;
    value.first = 4'b01zx;
    value.second = 3'bx01;
    return value === 7'b0100_x01;
  endfunction

  function automatic bit eval_nested_array_select_ok(input logic index,
                                                      input nested_array_t value);
    nested_row_t result = value[index];
    return result[0] === 3'bxxx && result[1] === 3'bxxx;
  endfunction

  function automatic bit eval_nested_array_write_ok(input logic index,
                                                     input nested_array_t value);
    nested_array_t original = value;
    value[index] = '{3'b000, 3'b000};
    return value[0][0] === original[0][0] && value[0][1] === original[0][1]
           && value[1][0] === original[1][0] && value[1][1] === original[1][1];
  endfunction

  function automatic bit eval_ascending_array_index_ok(input logic [1:0] index,
                                                        input ascending_array_t value);
    ascending_array_t original = value;
    logic [4:0] selected = value[index];
    value[index] = 5'b00000;
    return selected === 5'bxxxxx && value[1] === original[1] && value[2] === original[2]
           && value[3] === original[3];
  endfunction

  function automatic bit eval_descending_array_index_ok(input logic [1:0] index,
                                                         input descending_array_t value);
    descending_array_t original = value;
    logic [4:0] selected = value[index];
    value[index] = 5'b00000;
    return selected === 5'bxxxxx && value[3] === original[3] && value[2] === original[2]
           && value[1] === original[1];
  endfunction

  function automatic bit eval_real_array_select_ok(input logic index, input real_array_t value);
    return value[index] == 0.0;
  endfunction

  function automatic bit eval_string_array_select_ok(input logic index,
                                                      input string_array_t value);
    return value[index] == "";
  endfunction

  function automatic bit eval_string_array_literal_x_ok();
    string_array_t value;
    // verilator lint_off SELRANGE
    return value[1'bx] == "";
    // verilator lint_on SELRANGE
  endfunction

  localparam bit AND_X0 = eval_and(1'bx, 1'b0) === 1'b0;
  localparam bit AND_X1 = eval_and(1'bx, 1'b1) === 1'bx;
  localparam bit AND_Z1 = eval_and(1'bz, 1'b1) === 1'bx;
  localparam bit AND_X1_1 = eval_and_wide(2'bx1, 2'b01) === 1'b1;
  localparam bit AND_Z1_1 = eval_and_wide(2'bz1, 2'b01) === 1'b1;
  localparam bit BIT_CAST = eval_bit_cast(7'b10xz011) === 7'b1000011;
  localparam bit BIT_ASSIGN = eval_bit_assign(7'b10xz011) === 7'b1000011;
  localparam bit_vec_t BIT_ASSIGN_PARAM_VALUE = 1'bx ? 7'b1111111 : 7'b0000000;
  localparam bit OR_X0 = eval_or(1'bx, 1'b0) === 1'bx;
  localparam bit OR_X1 = eval_or(1'bx, 1'b1) === 1'b1;
  localparam bit OR_Z0 = eval_or(1'bz, 1'b0) === 1'bx;
  localparam bit OR_10 = eval_or(1'b1, 1'b0) === 1'b1;
  localparam bit OR_X1_0 = eval_or_wide(2'bx1, 2'b00) === 1'b1;
  localparam bit OR_Z1_0 = eval_or_wide(2'bz1, 2'b00) === 1'b1;
  localparam bit IF_00 = eval_if(1'b0, 1'b0) === 1'b1;
  localparam bit IF_01 = eval_if(1'b0, 1'b1) === 1'b1;
  localparam bit IF_10 = eval_if(1'b1, 1'b0) === 1'b0;
  localparam bit IF_11 = eval_if(1'b1, 1'b1) === 1'b1;
  localparam bit IF_X0 = eval_if(1'bx, 1'b0) === 1'bx;
  localparam bit IF_X1 = eval_if(1'bx, 1'b1) === 1'b1;
  localparam bit IF_Z0 = eval_if(1'bz, 1'b0) === 1'bx;
  localparam bit IF_X1_0 = eval_if_wide(2'bx1, 2'b00) === 1'b0;
  localparam bit IF_Z1_0 = eval_if_wide(2'bz1, 2'b00) === 1'b0;
  localparam bit IF_STMT_X0 = eval_if_stmt(2'bx0) == 1'b0;
  localparam bit IF_STMT_X1 = eval_if_stmt(2'bx1) == 1'b1;
  localparam bit IF_STMT_Z0 = eval_if_stmt(2'bz0) == 1'b0;
  localparam bit IF_STMT_Z1 = eval_if_stmt(2'bz1) == 1'b1;
  localparam bit WHILE_X0 = eval_while(2'bx0) == 0;
  localparam bit WHILE_X1 = eval_while(2'bx1) == 1;
  localparam bit WHILE_Z0 = eval_while(2'bz0) == 0;
  localparam bit WHILE_Z1 = eval_while(2'bz1) == 1;
  localparam bit DO_WHILE_X = eval_do_while(1'bx) == 1;
  localparam bit DO_WHILE_Z = eval_do_while(1'bz) == 1;
  localparam bit FOR_X0 = eval_for(2'bx0) == 0;
  localparam bit FOR_X1 = eval_for(2'bx1) == 1;
  localparam bit FOR_Z0 = eval_for(2'bz0) == 0;
  localparam bit FOR_Z1 = eval_for(2'bz1) == 1;
  localparam bit REPEAT_X = eval_repeat(32'bx) == 0;
  localparam bit REPEAT_Z = eval_repeat(32'bz) == 0;
  localparam bit REPEAT_KNOWN = eval_repeat(32'd2) == 2;
  localparam bit CASE_X = eval_case(3'b0x1) == 1;
  localparam bit CASE_Z = eval_case(3'b0z1) == 2;
  localparam bit CASE_KNOWN = eval_case(3'b001) == 3;
  localparam bit CASEZ_EXPR_Z = eval_casez(3'b1z0) == 1;
  localparam bit CASEZ_ITEM_Z = eval_casez(3'b1x1) == 2;
  localparam bit CASEZ_X_EXACT = eval_casez(3'b1x0) == 3;
  localparam bit CASEZ_X_NOT_WILD = eval_casez(3'b100) == 4;
  localparam bit CASEX_EXPR_X = eval_casex(3'b1x0) == 1;
  localparam bit CASEX_EXPR_Z = eval_casex(3'b1z0) == 1;
  localparam bit CASEX_ITEM_X = eval_casex(3'b001) == 2;
  localparam bit CASEX_ITEM_Z = eval_casex(3'b000) == 3;
  localparam bit CASE_INSIDE_X = eval_case_inside(3'b1x0) == 1;
  localparam bit CASE_INSIDE_Z = eval_case_inside(3'b0z1) == 2;
  localparam bit CASE_INSIDE_ITEM_X = eval_case_inside(3'b110) == 1;
  localparam bit CASE_INSIDE_ITEM_Z = eval_case_inside(3'b001) == 2;
  localparam bit CASE_INSIDE_DEFAULT = eval_case_inside(3'bx10) == 3;
  localparam bit CASE_INSIDE_RANGE = eval_case_inside_range(32'd3) == 1;
  localparam bit CASE_INSIDE_RANGE_LOW = eval_case_inside_range(32'd1) == 2;
  localparam bit CASE_INSIDE_RANGE_HIGH = eval_case_inside_range(32'd5) == 3;
  localparam bit CASE_INSIDE_RANGE_X = eval_case_inside_range(32'bx011) == 4;
  localparam bit CASE_INSIDE_RANGE_NARROW
      = eval_case_inside_range_narrow(15'd23) == 1
        && eval_case_inside_range_narrow(15'bx00000000010111) == 2;
  localparam bit CASE_INSIDE_RANGE_SIGNED = eval_case_inside_range_signed(-2) == 1;
  localparam bit CASE_INSIDE_RANGE_REAL = eval_case_inside_range_real(2.5) == 1;
  localparam bit PACKED_SELECT_X = eval_packed_select(2'b0x) === 1'bx;
  localparam bit PACKED_SELECT_Z = eval_packed_select(2'b0z) === 1'bx;
  localparam bit PACKED_WRITE_X = eval_packed_write(2'b0x) === 4'b1010;
  localparam bit PACKED_WRITE_Z = eval_packed_write(2'b0z) === 4'b1010;
  localparam bit PACKED_PART_SELECT_X = eval_packed_part_select(2'b0x) === 2'bxx;
  localparam bit PACKED_PART_SELECT_Z = eval_packed_part_select(2'b0z) === 2'bxx;
  localparam bit PACKED_PART_WRITE_X = eval_packed_part_write(2'b0x) === 4'b1010;
  localparam bit PACKED_PART_WRITE_Z = eval_packed_part_write(2'b0z) === 4'b1010;
  localparam bit COND_X = eval_cond(1'bx, 7'b10xz011, 7'b10xz101) === 7'b10xxxx1;
  localparam bit COND_Z = eval_cond(1'bz, 7'b10xz011, 7'b10xz101) === 7'b10xxxx1;
  localparam bit COND_WIDE
      = eval_cond_wide(1'bx, {1'b0, 31'h1234567, 1'b0},
                       {1'b1, 31'h1234567, 1'b1}) === {1'bx, 31'h1234567, 1'bx};
  localparam bit COND_SAME_Z
      = eval_cond(1'bx, 7'bzzzzzzz, 7'bzzzzzzz) === 7'bxxxxxxx;
  localparam bit STRING_TRUE = eval_string(1'b1) == "then";
  localparam bit STRING_FALSE = eval_string(1'b0) == "else";
  localparam bit STRING_X_SAME = eval_string_values(1'bx, "same", "same") == "same";
  localparam bit STRING_X_DIFF = eval_string_values(1'bx, "then", "else") == "";
  localparam bit STRING_X_VARIABLES = eval_string_variables(1'bx) == "";
  localparam bit REAL_TRUE = eval_real(1'b1) == 1.25;
  localparam bit REAL_FALSE = eval_real(1'b0) == 2.5;
  localparam bit REAL_X_SAME = eval_real_values(1'bx, 1.25, 1.25) == 1.25;
  localparam bit REAL_X_DIFF = eval_real_values(1'bx, 1.25, 2.5) == 0.0;
  localparam bit REAL_X_VARIABLES = eval_real_variables(1'bx) == 0.0;
  localparam array_t ARRAY_A = '{4'b1011, 4'b0011};
  localparam array_t ARRAY_B = '{4'b1001, 4'b0101};
  // verilator lint_off SELRANGE
  localparam logic [3:0] ARRAY_DIRECT_SELECT_X = ARRAY_A[1'bx];
  // verilator lint_on SELRANGE
  localparam bit ARRAY_X_OK = eval_array_ok(1'bx, ARRAY_A, ARRAY_B);
  localparam bit ARRAY_SELECT_X = eval_array_select(1'bx, ARRAY_A) === 4'bxxxx;
  localparam bit ARRAY_SELECT_Z = eval_array_select(1'bz, ARRAY_A) === 4'bxxxx;
  localparam bit ARRAY_WRITE_X = eval_array_write_ok(1'bx, ARRAY_A);
  localparam bit ARRAY_WRITE_Z = eval_array_write_ok(1'bz, ARRAY_A);
  localparam bit_array_t BIT_ARRAY = '{4'b1011, 4'b0011};
  localparam bit_array_t BIT_ARRAY_PARAM_XZ = eval_logic_array(4'bxxxx, 4'bzzzz);
  localparam bit BIT_ARRAY_PARAM_XZ_OK
      = BIT_ARRAY_PARAM_XZ[0] === 4'b0000 && BIT_ARRAY_PARAM_XZ[1] === 4'b0000;
  localparam bit BIT_ARRAY_SELECT_X = eval_bit_array_select_ok(1'bx, BIT_ARRAY);
  localparam bit BIT_ARRAY_SELECT_Z = eval_bit_array_select_ok(1'bz, BIT_ARRAY);
  localparam bit BIT_ARRAY_WRITE_X = eval_bit_array_write_ok(4'bxxxx, BIT_ARRAY);
  localparam bit BIT_ARRAY_WRITE_Z = eval_bit_array_write_ok(4'bzzzz, BIT_ARRAY);
  localparam bit BIT_ARRAY_ASSIGN = eval_bit_array_assign_ok();
  localparam bit UNPACKED_STRUCT_ASSIGN = eval_unpacked_struct_assign_ok();
  localparam unpacked_struct_t UNPACKED_STRUCT_COND_DEFAULT_X
      = eval_unpacked_struct_cond_default(1'bx);
  localparam unpacked_struct_t UNPACKED_STRUCT_COND_DEFAULT_Z
      = eval_unpacked_struct_cond_default(1'bz);
  localparam unpacked_struct_t UNPACKED_STRUCT_COND_SAME_X
      = eval_unpacked_struct_cond_same(1'bx);
  localparam unpacked_struct_t UNPACKED_STRUCT_COND_SAME_Z
      = eval_unpacked_struct_cond_same(1'bz);
  localparam bit UNPACKED_STRUCT_COND_DEFAULT_X_OK
      = UNPACKED_STRUCT_COND_DEFAULT_X.first === 4'b0000
        && UNPACKED_STRUCT_COND_DEFAULT_X.second === 3'bxxx;
  localparam bit UNPACKED_STRUCT_COND_DEFAULT_Z_OK
      = UNPACKED_STRUCT_COND_DEFAULT_Z.first === 4'b0000
        && UNPACKED_STRUCT_COND_DEFAULT_Z.second === 3'bxxx;
  localparam bit UNPACKED_STRUCT_COND_SAME_X_OK
      = UNPACKED_STRUCT_COND_SAME_X.first === 4'b1011
        && UNPACKED_STRUCT_COND_SAME_X.second === 3'b001;
  localparam bit UNPACKED_STRUCT_COND_SAME_Z_OK
      = UNPACKED_STRUCT_COND_SAME_Z.first === 4'b1011
        && UNPACKED_STRUCT_COND_SAME_Z.second === 3'b001;
  localparam bit CLASS_COND_SAME_X = eval_class_cond_same(1'bx) == null;
  localparam bit CLASS_COND_SAME_Z = eval_class_cond_same(1'bz) == null;
  localparam mixed_packed_struct_t MIXED_PACKED_STRUCT_PARAM = 7'bxxxx_x01;
  localparam bit MIXED_PACKED_STRUCT_PARAM_OK
      = MIXED_PACKED_STRUCT_PARAM.first === 4'b0000
        && MIXED_PACKED_STRUCT_PARAM.second === 3'bx01;
  localparam bit MIXED_PACKED_STRUCT_ASSIGN = eval_mixed_packed_struct_assign_ok();
  localparam bit MIXED_PACKED_STRUCT_READ = eval_mixed_packed_struct_read_ok();
  localparam logic [6:0] MIXED_PACKED_STRUCT_CAST_VALUE
      = 1'b1 ? mixed_packed_struct_t'(7'bxxxx_x01)
             : mixed_packed_struct_t'(7'bxxxx_x01);
  // IEEE 1800-2023 7.2.1 treats a mixed-state packed structure as one 4-state vector
  // when used as a whole. Per 6.22.2(c), it is equivalent to a same-sized 4-state
  // integral type, and the static cast follows assignment semantics per 6.24.1.
  // Thus no 4-state-to-2-state member conversion occurs because
  // there is no read from or write to the two-state field
  localparam bit MIXED_PACKED_STRUCT_CAST
      = MIXED_PACKED_STRUCT_CAST_VALUE === 7'bxxxx_x01;
  localparam bit PACKED_2STATE_STRUCT_DEFAULT_X = eval_packed_2state_struct_default(1'bx);
  localparam bit PACKED_2STATE_STRUCT_DEFAULT_Z = eval_packed_2state_struct_default(1'bz);
  localparam bit PACKED_BIT_ARRAY_DEFAULT = eval_packed_bit_array_default();
  localparam bit PACKED_LOGIC_ARRAY_DEFAULT = eval_packed_logic_array_default();
  localparam bit PACKED_4STATE_STRUCT_DEFAULT_X = eval_packed_4state_struct_default(1'bx);
  localparam bit PACKED_4STATE_STRUCT_DEFAULT_Z = eval_packed_4state_struct_default(1'bz);
  localparam bit MIXED_PACKED_STRUCT_DEFAULT_X = eval_mixed_packed_struct_default(1'bx);
  localparam bit MIXED_PACKED_STRUCT_DEFAULT_Z = eval_mixed_packed_struct_default(1'bz);
  localparam bit PACKED_NESTED_2STATE_STRUCT_DEFAULT_X
      = eval_packed_nested_2state_struct_default(1'bx);
  localparam bit PACKED_NESTED_2STATE_STRUCT_DEFAULT_Z
      = eval_packed_nested_2state_struct_default(1'bz);
  localparam bit PACKED_NESTED_MIXED_STRUCT_DEFAULT_X
      = eval_packed_nested_mixed_struct_default(1'bx);
  localparam bit PACKED_NESTED_MIXED_STRUCT_DEFAULT_Z
      = eval_packed_nested_mixed_struct_default(1'bz);
  localparam bit PACKED_NESTED_4STATE_STRUCT_DEFAULT_X
      = eval_packed_nested_4state_struct_default(1'bx);
  localparam bit PACKED_NESTED_4STATE_STRUCT_DEFAULT_Z
      = eval_packed_nested_4state_struct_default(1'bz);
  localparam bit PACKED_STRUCT_X
      = eval_packed_struct(1'bx, '{4'b1011, 3'b001}, '{4'b1001, 3'b011})
        === packed_struct_t'{4'b10x1, 3'b0x1};
  localparam nested_array_t NESTED_ARRAY_A = '{'{3'b101, 3'b001}, '{3'b011, 3'b110}};
  localparam nested_array_t NESTED_ARRAY_B = '{'{3'b100, 3'b011}, '{3'b111, 3'b100}};
  localparam bit NESTED_ARRAY_X_OK
      = eval_nested_array_ok(1'bx, NESTED_ARRAY_A, NESTED_ARRAY_B);
  localparam bit NESTED_ARRAY_SELECT_X = eval_nested_array_select_ok(1'bx, NESTED_ARRAY_A);
  localparam bit NESTED_ARRAY_SELECT_Z = eval_nested_array_select_ok(1'bz, NESTED_ARRAY_A);
  localparam bit NESTED_ARRAY_WRITE_X = eval_nested_array_write_ok(1'bx, NESTED_ARRAY_A);
  localparam bit NESTED_ARRAY_WRITE_Z = eval_nested_array_write_ok(1'bz, NESTED_ARRAY_A);
  localparam ascending_array_t ASCENDING_ARRAY = '{5'b10101, 5'b00111, 5'b11000};
  localparam bit ASCENDING_ARRAY_INDEX_X
      = eval_ascending_array_index_ok(2'b0x, ASCENDING_ARRAY);
  localparam bit ASCENDING_ARRAY_INDEX_Z
      = eval_ascending_array_index_ok(2'b0z, ASCENDING_ARRAY);
  localparam descending_array_t DESCENDING_ARRAY = '{5'b10101, 5'b00111, 5'b11000};
  localparam bit DESCENDING_ARRAY_INDEX_X
      = eval_descending_array_index_ok(2'b0x, DESCENDING_ARRAY);
  localparam bit DESCENDING_ARRAY_INDEX_Z
      = eval_descending_array_index_ok(2'b0z, DESCENDING_ARRAY);
  localparam real_array_t REAL_ARRAY = '{1.25, 2.5};
  localparam bit REAL_ARRAY_SELECT_X = eval_real_array_select_ok(1'bx, REAL_ARRAY);
  localparam bit REAL_ARRAY_SELECT_Z = eval_real_array_select_ok(1'bz, REAL_ARRAY);
  localparam string_array_t STRING_ARRAY_A = '{"same", "left"};
  localparam string_array_t STRING_ARRAY_B = '{"same", "right"};
  localparam bit STRING_ARRAY_X_OK
      = eval_string_array_ok(1'bx, STRING_ARRAY_A, STRING_ARRAY_B);
  localparam bit STRING_ARRAY_SELECT_X = eval_string_array_select_ok(1'bx, STRING_ARRAY_A);
  localparam bit STRING_ARRAY_SELECT_Z = eval_string_array_select_ok(1'bz, STRING_ARRAY_A);
  localparam bit STRING_ARRAY_LITERAL_X = eval_string_array_literal_x_ok();
  localparam bit COND_X_1_0 = 1'bx ? 1'b1 : 1'b0;

  initial begin
    `checkh({default_is_x, default_is_z}, 2'b10);
    `checkh({explicit_is_x, explicit_is_z}, 2'b10);
    `checkh({x_is_x, x_is_z}, 2'b10);
    `checkh({z_is_x, z_is_z}, 2'b01);
    `checkh({AND_X0, AND_X1, AND_Z1, AND_X1_1, AND_Z1_1}, 5'b11111);
    `checkh({BIT_CAST, BIT_ASSIGN}, 2'b11);
    `checkh(BIT_ASSIGN_PARAM_VALUE, 7'b0000000);
    `checkh({OR_X0, OR_X1, OR_Z0, OR_10, OR_X1_0, OR_Z1_0}, 6'b111111);
    `checkh({IF_00, IF_01, IF_10, IF_11, IF_X0, IF_X1, IF_Z0, IF_X1_0, IF_Z1_0},
            9'b111111111);
    `checkh({IF_STMT_X0, IF_STMT_X1, IF_STMT_Z0, IF_STMT_Z1}, 4'b1111);
    `checkh({WHILE_X0, WHILE_X1, WHILE_Z0, WHILE_Z1, DO_WHILE_X, DO_WHILE_Z}, 6'b111111);
    `checkh({FOR_X0, FOR_X1, FOR_Z0, FOR_Z1}, 4'b1111);
    `checkh({REPEAT_X, REPEAT_Z, REPEAT_KNOWN}, 3'b111);
    `checkh({CASE_X, CASE_Z, CASE_KNOWN}, 3'b111);
    `checkh({CASEZ_EXPR_Z, CASEZ_ITEM_Z, CASEZ_X_EXACT, CASEZ_X_NOT_WILD}, 4'b1111);
    `checkh({CASEX_EXPR_X, CASEX_EXPR_Z, CASEX_ITEM_X, CASEX_ITEM_Z}, 4'b1111);
    `checkh({CASE_INSIDE_X, CASE_INSIDE_Z, CASE_INSIDE_ITEM_X, CASE_INSIDE_ITEM_Z,
             CASE_INSIDE_DEFAULT}, 5'b11111);
    `checkh({CASE_INSIDE_RANGE, CASE_INSIDE_RANGE_LOW, CASE_INSIDE_RANGE_HIGH,
             CASE_INSIDE_RANGE_X}, 4'b1111);
    `checkh({CASE_INSIDE_RANGE_NARROW, CASE_INSIDE_RANGE_SIGNED, CASE_INSIDE_RANGE_REAL}, 3'b111);
    `checkh({PACKED_SELECT_X, PACKED_SELECT_Z, PACKED_WRITE_X, PACKED_WRITE_Z}, 4'b1111);
    `checkh({PACKED_PART_SELECT_X, PACKED_PART_SELECT_Z, PACKED_PART_WRITE_X,
             PACKED_PART_WRITE_Z}, 4'b1111);
    `checkh(ARRAY_DIRECT_SELECT_X, 4'bxxxx);
    `checkh({ARRAY_SELECT_X, ARRAY_SELECT_Z, ARRAY_WRITE_X, ARRAY_WRITE_Z}, 4'b1111);
    `checkh({BIT_ARRAY_SELECT_X, BIT_ARRAY_SELECT_Z, BIT_ARRAY_WRITE_X, BIT_ARRAY_WRITE_Z,
             BIT_ARRAY_ASSIGN, NESTED_ARRAY_SELECT_X, NESTED_ARRAY_SELECT_Z}, 7'b1111111);
    `checkh(BIT_ARRAY_PARAM_XZ_OK, 1'b1);
    `checkh({UNPACKED_STRUCT_ASSIGN, UNPACKED_STRUCT_COND_DEFAULT_X_OK,
             UNPACKED_STRUCT_COND_DEFAULT_Z_OK, UNPACKED_STRUCT_COND_SAME_X_OK,
             UNPACKED_STRUCT_COND_SAME_Z_OK, CLASS_COND_SAME_X, CLASS_COND_SAME_Z}, 7'b1111111);
    `checkh({MIXED_PACKED_STRUCT_PARAM_OK, MIXED_PACKED_STRUCT_ASSIGN, MIXED_PACKED_STRUCT_READ,
             MIXED_PACKED_STRUCT_CAST}, 4'b1111);
    `checkh({PACKED_2STATE_STRUCT_DEFAULT_X, PACKED_2STATE_STRUCT_DEFAULT_Z,
             PACKED_4STATE_STRUCT_DEFAULT_X, PACKED_4STATE_STRUCT_DEFAULT_Z,
             MIXED_PACKED_STRUCT_DEFAULT_X, MIXED_PACKED_STRUCT_DEFAULT_Z}, 6'b111111);
    `checkh({PACKED_BIT_ARRAY_DEFAULT, PACKED_LOGIC_ARRAY_DEFAULT}, 2'b11);
    `checkh({PACKED_NESTED_2STATE_STRUCT_DEFAULT_X, PACKED_NESTED_2STATE_STRUCT_DEFAULT_Z,
             PACKED_NESTED_MIXED_STRUCT_DEFAULT_X, PACKED_NESTED_MIXED_STRUCT_DEFAULT_Z,
             PACKED_NESTED_4STATE_STRUCT_DEFAULT_X, PACKED_NESTED_4STATE_STRUCT_DEFAULT_Z},
            6'b111111);
    `checkh({NESTED_ARRAY_WRITE_X, NESTED_ARRAY_WRITE_Z}, 2'b11);
    `checkh({ASCENDING_ARRAY_INDEX_X, ASCENDING_ARRAY_INDEX_Z, DESCENDING_ARRAY_INDEX_X,
             DESCENDING_ARRAY_INDEX_Z}, 4'b1111);
    `checkh({REAL_ARRAY_SELECT_X, REAL_ARRAY_SELECT_Z, STRING_ARRAY_SELECT_X,
             STRING_ARRAY_SELECT_Z, STRING_ARRAY_LITERAL_X}, 5'b11111);
    `checkh({COND_X, COND_Z, COND_WIDE, COND_SAME_Z}, 4'b1111);
    `checkh({STRING_TRUE, STRING_FALSE, STRING_X_SAME, STRING_X_DIFF, STRING_X_VARIABLES},
            5'b11111);
    `checkh({REAL_TRUE, REAL_FALSE, REAL_X_SAME, REAL_X_DIFF, REAL_X_VARIABLES}, 5'b11111);
    `checkh({ARRAY_X_OK, PACKED_STRUCT_X, NESTED_ARRAY_X_OK, STRING_ARRAY_X_OK}, 4'b1111);
    `checkh(COND_X_1_0, 1'b0);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
