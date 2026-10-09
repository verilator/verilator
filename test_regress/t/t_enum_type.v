// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;

  typedef enum logic signed [6:0] {
    SIGNED_NEG = -7'sd3,
    SIGNED_ZERO = 0,
    SIGNED_POS = 7'sd63
  } signed_t;

  typedef enum bit [2:0] {
    UNSIGNED_ZERO = 0,
    UNSIGNED_TWO = 2,
    UNSIGNED_SEVEN = 7
  } unsigned_t;

  typedef enum int {
    INT_ZERO = 0,
    INT_ONE = 1
  } int_t;

  typedef struct packed {
    signed_t signed_e;
    unsigned_t unsigned_e;
  } struct_t;

  initial begin
    signed_t signed_e;
    unsigned_t unsigned_e;
    int_t int_e;
    struct_t str;
    int int_value;
    logic signed [6:0] signed_value;
    logic [2:0] unsigned_value;

    signed_e = SIGNED_NEG;
    unsigned_e = UNSIGNED_SEVEN;
    int_e = INT_ONE;

    int_value = int'(signed_e);
    `checkd(int_value, -3);
    int_value = int'(unsigned_e);
    `checkd(int_value, 7);
    signed_value = signed_e;
    `checkd(signed_value, -3);
    unsigned_value = unsigned_e;
    `checkd(unsigned_value, 7);
    int_value = int'(signed_e) + int'(unsigned_e);
    `checkd(int_value, 4);
    `checkd(int'(signed_e) < int'(unsigned_e), 1);

    signed_e = signed_t'(unsigned_e);
    `checkd(signed_e, 7);
    unsigned_e = unsigned_t'(SIGNED_NEG);
    `checkd(unsigned_e, 5);
    int_e = int_t'(unsigned_e);
    `checkd(int_e, 5);
    signed_e = signed_t'(int'(unsigned_t'(SIGNED_NEG)));
    `checkd(signed_e, 5);
    unsigned_e = unsigned_t'(signed_t'(int_e + 3));
    `checkd(unsigned_e, 0);
    int_e = int_t'(signed_t'(unsigned_t'(SIGNED_NEG)));
    `checkd(int_e, 5);
    signed_e = signed_t'(int_e + 3);
    `checkd(signed_e, 8);
    unsigned_e = unsigned_t'(signed_e);
    `checkd(unsigned_e, 0);
    signed_e = signed_t'(int'(unsigned_e) - 7);
    `checkd(signed_e, -7);

    str.signed_e = signed_t'(unsigned_e);
    str.unsigned_e = unsigned_t'(str.signed_e);
    `checkd(str.signed_e, 0);
    `checkd(str.unsigned_e, 0);
    int_e = int_t'(str.unsigned_e);
    `checkd(int_e, 0);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
