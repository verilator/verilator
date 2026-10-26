// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv, expv) \
    do if ((gotv) !== (expv)) begin \
        $write("%%Error: %s:%0d: got=%0d exp=%0d\n", `__FILE__, `__LINE__, (gotv), (expv)); \
        `stop; \
    end while (0);
// verilog_format: on

module t;

  // Issue #8615 standalone reproducer
  byte repro_a;
  bit signed [7:0] repro_b;
  localparam bit REPRO_EQ = (type(repro_a) == type(repro_b));
  localparam bit REPRO_NE = (type(repro_a) != type(repro_b));
  localparam bit REPRO_CE = (type(repro_a) === type(repro_b));
  localparam bit REPRO_CN = (type(repro_a) !== type(repro_b));

  byte v_byte;
  byte unsigned v_byte_u;
  shortint v_shortint;
  shortint unsigned v_shortint_u;
  int v_int;
  int unsigned v_int_u;
  longint v_longint;
  longint unsigned v_longint_u;
  integer v_integer;
  integer unsigned v_integer_u;
  time v_time;

  bit signed [7:0] v_bit_s8;
  bit signed [7:0] v_bit_s8_copy;
  /* verilator lint_off ASCRANGE */
  bit signed [0:7] v_bit_s8_asc;
  /* verilator lint_on ASCRANGE */
  bit unsigned [7:0] v_bit_u8;
  logic signed [7:0] v_logic_s8;
  bit signed [6:0] v_bit_s7;
  bit signed [8:1] v_bit_s8_offset;

  bit v_scalar_bit;
  bit [0:0] v_vec_bit_1;
  logic v_scalar_logic;
  logic [0:0] v_vec_logic_1;

  wire [7:0] v_implicit_8;
  logic [7:0] v_logic_8;
  reg [7:0] v_reg_8;

  logic [1:0][7:0] v_pack_a;
  logic [1:0][7:0] v_pack_b;
  logic [2:1][7:0] v_pack_off;
  logic [1:0][6:0] v_pack_diff_sub;

  bit signed [15:0] v_bit_s16;
  bit unsigned [15:0] v_bit_u16;

  bit signed [31:0] v_bit_s32;
  bit unsigned [31:0] v_bit_u32;
  logic signed [31:0] v_logic_s32;
  logic unsigned [31:0] v_logic_u32;

  bit signed [63:0] v_bit_s64;
  bit unsigned [63:0] v_bit_u64;
  logic [63:0] v_logic_64;
  logic unsigned [63:0] v_logic_u64;
  logic signed [63:0] v_logic_s64;

  typedef byte my_byte_t;
  typedef bit signed [7:0] my_vec_t;
  my_byte_t v_my_byte;
  my_vec_t v_my_vec;

  typedef struct packed {
    logic [7:0] a;
  } my_struct_a_t;

  typedef struct packed {
    logic [7:0] a;
  } my_struct_b_t;

  typedef enum logic [1:0] {
    E0_A,
    E1_A
  } my_enum_a_t;

  typedef enum logic [1:0] {
    E0_B,
    E1_B
  } my_enum_b_t;

  my_struct_a_t v_struct_a;
  my_struct_a_t v_struct_a2;
  my_struct_b_t v_struct_b;
  my_enum_a_t v_enum_a;
  my_enum_a_t v_enum_a2;
  my_enum_b_t v_enum_b;

  int v_dyn_int[];
  bit signed [31:0] v_dyn_s32[];
  /* verilator lint_off ASCRANGE */
  bit signed [0:31] v_dyn_s32_asc[];
  /* verilator lint_on ASCRANGE */
  int v_queue_int[$];
  bit signed [31:0] v_queue_s32[$];
  /* verilator lint_off ASCRANGE */
  bit signed [0:31] v_queue_s32_asc[$];
  /* verilator lint_on ASCRANGE */

  int v_assoc_a[int];
  bit signed [31:0] v_assoc_b[bit signed [31:0]];
  int v_assoc_key_mismatch[string];
  string v_assoc_elem_mismatch[int];

  int v_wild_a[*];
  bit signed [31:0] v_wild_b[*];
  string v_wild_c[*];

  typedef int my_dyn_t[];
  typedef bit signed [31:0] my_dyn_vec_t[];
  my_dyn_t v_tdef_dyn_a;
  my_dyn_vec_t v_tdef_dyn_b;

  typedef int my_queue_t[$];
  typedef bit signed [31:0] my_queue_vec_t[$];
  my_queue_t v_tdef_queue_a;
  my_queue_vec_t v_tdef_queue_b;

  byte v_byte_arr[4];
  bit signed [7:0] v_bit_s8_arr[4];
  bit signed [7:0] v_bit_s8_arr_rev[3:0];

  byte v_byte_c_arr[3:0];
  /* verilator lint_off ASCRANGE */
  byte v_byte_asc_arr[0:3];
  byte v_byte_off_arr[1:4];
  /* verilator lint_on ASCRANGE */
  byte v_byte_expr_arr[4-1:0];
  byte v_byte_c3_arr[3:0];

  localparam bit LP_BYTE_EQ = (type(v_byte) == type(v_bit_s8));
  localparam bit LP_BYTE_NE = (type(v_byte) != type(v_bit_s8));
  localparam bit LP_BYTE_CE = (type(v_byte) === type(v_bit_s8));
  localparam bit LP_BYTE_CN = (type(v_byte) !== type(v_bit_s8));
  localparam bit LP_BYTE_REV_EQ = (type(v_bit_s8) == type(v_byte));

  localparam bit LP_BYTE_U_EQ = (type(v_byte_u) == type(v_bit_u8));
  localparam bit LP_BYTE_U_NE = (type(v_byte_u) != type(v_bit_u8));
  localparam bit LP_SHORTINT_U_EQ = (type(v_shortint_u) == type(v_bit_u16));
  localparam bit LP_INT_U_EQ = (type(v_int_u) == type(v_bit_u32));
  localparam bit LP_LONGINT_U_EQ = (type(v_longint_u) == type(v_bit_u64));
  localparam bit LP_INTEGER_U_EQ = (type(v_integer_u) == type(v_logic_u32));

  localparam bit LP_SHORTINT_EQ = (type(v_shortint) == type(v_bit_s16));
  localparam bit LP_INT_EQ = (type(v_int) == type(v_bit_s32));
  localparam bit LP_LONGINT_EQ = (type(v_longint) == type(v_bit_s64));
  localparam bit LP_INTEGER_EQ = (type(v_integer) == type(v_logic_s32));
  localparam bit LP_TIME_EQ = (type(v_time) == type(v_logic_u64));
  localparam bit LP_TIME_IMP_EQ = (type(v_time) == type(v_logic_64));
  localparam bit LP_TYPEDEF_EQ = (type(v_my_byte) == type(v_my_vec));

  localparam bit LP_BYTE_ASC_EQ = (type(v_byte) == type(v_bit_s8_asc));
  localparam bit LP_BYTE_U8_EQ = (type(v_byte) == type(v_bit_u8));
  localparam bit LP_BYTE_LOGIC_EQ = (type(v_byte) == type(v_logic_s8));
  localparam bit LP_BYTE_S7_EQ = (type(v_byte) == type(v_bit_s7));
  localparam bit LP_BYTE_OFFSET_EQ = (type(v_byte) == type(v_bit_s8_offset));
  localparam bit LP_TIME_BIT_EQ = (type(v_time) == type(v_bit_u64));
  localparam bit LP_TIME_SIGNED_EQ = (type(v_time) == type(v_logic_s64));
  localparam bit LP_ARR_BRACKET_EQ = (type(v_byte_c_arr) == type(v_byte_asc_arr));
  localparam bit LP_ARR_EXPR_EQ = (type(v_byte_expr_arr) == type(v_byte_c3_arr));
  localparam bit LP_ARR_DIR_EQ = (type(v_byte_c_arr) == type(v_byte_arr));
  localparam bit LP_ARR_OFF_EQ = (type(v_byte_off_arr) == type(v_byte_asc_arr));

  int case_ok;

  initial begin
    `checkd(REPRO_EQ, 1'b1);
    `checkd(REPRO_NE, 1'b0);
    `checkd(REPRO_CE, 1'b1);
    `checkd(REPRO_CN, 1'b0);
    `checkd(type(repro_a) == type(repro_b), 1'b1);
    `checkd(type(repro_a) != type(repro_b), 1'b0);
    `checkd(type(repro_a) === type(repro_b), 1'b1);
    `checkd(type(repro_a) !== type(repro_b), 1'b0);

    `checkd(LP_BYTE_EQ, 1'b1);
    `checkd(LP_BYTE_NE, 1'b0);
    `checkd(LP_BYTE_CE, 1'b1);
    `checkd(LP_BYTE_CN, 1'b0);
    `checkd(LP_BYTE_REV_EQ, 1'b1);
    `checkd(type(v_byte) == type(v_bit_s8), 1'b1);
    `checkd(type(v_byte) != type(v_bit_s8), 1'b0);
    `checkd(type(v_byte) === type(v_bit_s8), 1'b1);
    `checkd(type(v_byte) !== type(v_bit_s8), 1'b0);
    `checkd(type(v_bit_s8) == type(v_byte), 1'b1);

    `checkd(LP_BYTE_U_EQ, 1'b1);
    `checkd(LP_BYTE_U_NE, 1'b0);
    `checkd(type(v_byte_u) == type(v_bit_u8), 1'b1);
    `checkd(type(v_byte_u) != type(v_bit_u8), 1'b0);
    `checkd(type(v_byte_u) == type(v_bit_s8), 1'b0);

    `checkd(LP_SHORTINT_U_EQ, 1'b1);
    `checkd(type(v_shortint_u) == type(v_bit_u16), 1'b1);

    `checkd(LP_INT_U_EQ, 1'b1);
    `checkd(type(v_int_u) == type(v_bit_u32), 1'b1);

    `checkd(LP_LONGINT_U_EQ, 1'b1);
    `checkd(type(v_longint_u) == type(v_bit_u64), 1'b1);

    `checkd(LP_INTEGER_U_EQ, 1'b1);
    `checkd(type(v_integer_u) == type(v_logic_u32), 1'b1);

    `checkd(LP_SHORTINT_EQ, 1'b1);
    `checkd(type(v_shortint) == type(v_bit_s16), 1'b1);
    `checkd(type(v_bit_s16) == type(v_shortint), 1'b1);

    `checkd(LP_INT_EQ, 1'b1);
    `checkd(type(v_int) == type(v_bit_s32), 1'b1);
    `checkd(type(v_bit_s32) == type(v_int), 1'b1);

    `checkd(LP_LONGINT_EQ, 1'b1);
    `checkd(type(v_longint) == type(v_bit_s64), 1'b1);
    `checkd(type(v_bit_s64) == type(v_longint), 1'b1);

    `checkd(LP_INTEGER_EQ, 1'b1);
    `checkd(type(v_integer) == type(v_logic_s32), 1'b1);
    `checkd(type(v_logic_s32) == type(v_integer), 1'b1);

    `checkd(LP_TIME_EQ, 1'b1);
    `checkd(type(v_time) == type(v_logic_u64), 1'b1);
    `checkd(type(v_logic_u64) == type(v_time), 1'b1);
    `checkd(LP_TIME_IMP_EQ, 1'b1);
    `checkd(type(v_time) == type(v_logic_64), 1'b1);

    `checkd(LP_TYPEDEF_EQ, 1'b1);
    `checkd(type(v_my_byte) == type(v_my_vec), 1'b1);

    `checkd(LP_TIME_BIT_EQ, 1'b0);
    `checkd(type(v_time) == type(v_bit_u64), 1'b0);
    `checkd(LP_TIME_SIGNED_EQ, 1'b0);
    `checkd(type(v_time) == type(v_logic_s64), 1'b0);

    `checkd(type(v_byte_arr) == type(v_bit_s8_arr), 1'b1);
    `checkd(type(v_byte_arr) != type(v_bit_s8_arr), 1'b0);
    `checkd(type(v_byte_arr) == type(v_bit_s8_arr_rev), 1'b0);

    `checkd(LP_ARR_BRACKET_EQ, 1'b0);
    `checkd(type(v_byte_c_arr) == type(v_byte_asc_arr), 1'b0);
    `checkd(LP_ARR_EXPR_EQ, 1'b1);
    `checkd(type(v_byte_expr_arr) == type(v_byte_c3_arr), 1'b1);
    `checkd(LP_ARR_DIR_EQ, 1'b0);
    `checkd(type(v_byte_c_arr) == type(v_byte_arr), 1'b0);
    `checkd(LP_ARR_OFF_EQ, 1'b0);
    `checkd(type(v_byte_off_arr) == type(v_byte_asc_arr), 1'b0);

    `checkd(LP_BYTE_ASC_EQ, 1'b0);
    `checkd(type(v_byte) == type(v_bit_s8_asc), 1'b0);

    `checkd(LP_BYTE_U8_EQ, 1'b0);
    `checkd(type(v_byte) == type(v_bit_u8), 1'b0);

    `checkd(LP_BYTE_LOGIC_EQ, 1'b0);
    `checkd(type(v_byte) == type(v_logic_s8), 1'b0);

    `checkd(LP_BYTE_S7_EQ, 1'b0);
    `checkd(type(v_byte) == type(v_bit_s7), 1'b0);

    `checkd(LP_BYTE_OFFSET_EQ, 1'b0);
    `checkd(type(v_byte) == type(v_bit_s8_offset), 1'b0);

    `checkd(type(v_struct_a) == type(v_struct_a2), 1'b1);
    `checkd(type(v_struct_a) == type(v_struct_b), 1'b0);
    `checkd(type(v_enum_a) == type(v_enum_a2), 1'b1);
    `checkd(type(v_enum_a) == type(v_enum_b), 1'b0);

    `checkd(type(v_dyn_int) == type(v_dyn_s32), 1'b1);
    `checkd(type(v_dyn_int) == type(v_dyn_s32_asc), 1'b0);
    `checkd(type(v_queue_int) == type(v_queue_s32), 1'b1);
    `checkd(type(v_queue_int) == type(v_queue_s32_asc), 1'b0);

    `checkd(type(v_integer) == type(v_bit_s32), 1'b0);
    `checkd(type(v_int) == type(v_logic_s32), 1'b0);

    `checkd(type(v_bit_s8) == type(v_bit_s8_copy), 1'b1);
    `checkd(type(v_bit_s8) == type(v_bit_s8_offset), 1'b0);
    `checkd(type(v_bit_s8) == type(v_bit_s8_asc), 1'b0);

    `checkd(type(v_scalar_bit) == type(v_vec_bit_1), 1'b0);
    `checkd(type(v_scalar_logic) == type(v_vec_logic_1), 1'b0);

    `checkd(type(v_implicit_8) == type(v_logic_8), 1'b1);
    `checkd(type(v_reg_8) == type(v_logic_8), 1'b1);

    `checkd(type(v_pack_a) == type(v_pack_b), 1'b1);
    `checkd(type(v_pack_a) == type(v_pack_off), 1'b0);
    `checkd(type(v_pack_a) == type(v_pack_diff_sub), 1'b0);

    `checkd(type(v_assoc_a) == type(v_assoc_b), 1'b1);
    `checkd(type(v_assoc_a) == type(v_assoc_key_mismatch), 1'b0);
    `checkd(type(v_assoc_a) == type(v_assoc_elem_mismatch), 1'b0);

    `checkd(type(v_wild_a) == type(v_wild_b), 1'b1);
    `checkd(type(v_wild_a) == type(v_wild_c), 1'b0);

    `checkd(type(v_tdef_dyn_a) == type(v_tdef_dyn_b), 1'b1);
    `checkd(type(v_tdef_queue_a) == type(v_tdef_queue_b), 1'b1);

    case (type(v_byte))
      type(v_bit_s8_asc): case_ok = 1;
      type(v_bit_u8): case_ok = 2;
      type(v_logic_s8): case_ok = 3;
      type(v_bit_s8): case_ok = 4;
      default: case_ok = 0;
    endcase
    `checkd(case_ok, 4);

    case (type(v_bit_s8))
      type(v_bit_s8_asc): case_ok = 1;
      type(v_byte): case_ok = 2;
      default: case_ok = 0;
    endcase
    `checkd(case_ok, 2);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
