// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;

  localparam int unsigned XLEN = 32;

  string pkt;
  int unsigned idx;
  logic [XLEN-1:0] val;
  int code;
  longint signed scanned;
  real scanned_real;
  byte next_char;

  reg [255:0] line;
  reg [63:0] token;

  initial begin
    // All digits after % is to get line coverage in verilated.cpp
    code = $sscanf("P20=4cff0000", "P%h=%80123456789h", idx, val);
    `checkh(code, 2);
    `checkh(idx, 32'h20);
    `checkh(val, 32'h4cff0000);

    line = "Hello 1 2 3";
    code = $sscanf(line, "%s %x\n", token, idx);
    `checkh(code, 2);
    `checks(token, "\0\0\0Hello");
    `checkh(idx, 1);

    // Input ends after some conversions: return the number assigned, not EOF
    code = $sscanf("Hi 5", "%s %d %d", token, idx, val);
    `checkh(code, 2);
    `checks(token, "\0\0\0\0\0\0Hi");
    `checkh(idx, 5);

    // Matching failure before the first conversion: 0
    code = $sscanf("Hi", "%d", idx);
    `checkh(code, 0);

    // Input ends before the first conversion: EOF
    code = $sscanf("", "%d", idx);
    `checkh(code, -1);

    // Decimal digit separators, including leading and trailing underscores.
    code = $sscanf("10_000_000", "%d", scanned);
    `checkd(code, 1);
    `checkd(scanned, 10_000_000);
    code = $sscanf("-10_000_000", "%d", scanned);
    `checkd(code, 1);
    `checkd(scanned, -10_000_000);
    code = $sscanf("1_234", "%d", idx);
    `checkd(code, 1);
    `checkd(idx, 1_234);
    code = $sscanf("_1_234", "%d", scanned);
    `checkd(code, 1);
    `checkd(scanned, 1_234);
    code = $sscanf("1_234_", "%d", scanned);
    `checkd(code, 1);
    `checkd(scanned, 1_234);

    // An underscore-only field must not assign a value or count as a conversion.
    scanned = 99;
    code = $sscanf("_", "%d", scanned);
    `checkd(code, -1);
    `checkd(scanned, 99);
    code = $sscanf("_ ", "%d", scanned);
    `checkd(code, 0);
    `checkd(scanned, 99);
    code = $sscanf("7 _", "%d %d", idx, scanned);
    `checkd(code, 1);
    `checkd(idx, 7);
    `checkd(scanned, 99);

    // IEEE 1800-2023 Table 21-7 excludes underscores from floating-point fields.
    // Leave the underscore unread so the following conversion can consume it.
    code = $sscanf("1_234.5", "%f%c", scanned_real, next_char);
    `checkd(code, 2);
    `checkh($realtobits(scanned_real), $realtobits(1.0));
    `checkd(next_char, 8'h5f);
    code = $sscanf("1.25_e2", "%e%c", scanned_real, next_char);
    `checkd(code, 2);
    `checkh($realtobits(scanned_real), $realtobits(1.25));
    `checkd(next_char, 8'h5f);
    code = $sscanf("1.25e1_0", "%g%c", scanned_real, next_char);
    `checkd(code, 2);
    `checkh($realtobits(scanned_real), $realtobits(12.5));
    `checkd(next_char, 8'h5f);
    scanned_real = 99.0;
    code = $sscanf("_", "%f", scanned_real);
    `checkd(code, 0);
    `checkh($realtobits(scanned_real), $realtobits(99.0));

    $finish;
  end

endmodule
