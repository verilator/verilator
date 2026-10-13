// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Tests constant pool entries created at different compilation stages.
// - 'color.name()' makes V3Width create the enum name table in the constant pool, before V3Scope.
// - 'sparse.name()' needs an associative array, as the enum values are too far apart for a table.
// - Array parameters in functions are moved into the constant pool by V3Task, after V3Scope.
// - The variably indexed wide constant is extracted into the constant pool by V3Premit.

typedef enum logic [1:0] {
  RED,
  GREEN,
  BLUE
} color_e;

typedef enum logic [31:0] {
  LOW = 32'h1,
  HIGH = 32'h1000_0000
} sparse_e;

package pkg;
  // Distinct type, but same values and names as '$unit::sparse_e', so same name map
  typedef enum logic [31:0] {
    LOW = 32'h1,
    HIGH = 32'h1000_0000
  } sparse_e;
endpackage

function automatic logic [31:0] getWord(logic [2:0] i);
  // Same value as 'WIDE' below
  localparam bit [255:0] WORDS = {
    32'h8888_8888,
    32'h7777_7777,
    32'h6666_6666,
    32'h5555_5555,
    32'h4444_4444,
    32'h3333_3333,
    32'h2222_2222,
    32'h1111_1111
  };
  return WORDS[32*i+:32];
endfunction

function automatic logic [7:0] getDigit(logic [3:0] d);
  localparam logic [7:0] DIGITS[10] = '{"0", "1", "2", "3", "4", "5", "6", "7", "8", "9"};
  return DIGITS[d];
endfunction

function automatic string getName(logic [1:0] c);
  // Same as the enum name table: indexed by the enum value, empty for unused values
  localparam string NAMES[3:0] = '{"", "BLUE", "GREEN", "RED"};
  return NAMES[c];
endfunction

module t;
  logic clk = 0;
  always #5 clk = ~clk;

  integer cyc = 0;
  color_e color;
  string names[3] = '{"RED", "GREEN", "BLUE"};
  sparse_e sparse;
  pkg::sparse_e pkgSparse;
  localparam bit [255:0] WIDE = {
    32'h8888_8888,
    32'h7777_7777,
    32'h6666_6666,
    32'h5555_5555,
    32'h4444_4444,
    32'h3333_3333,
    32'h2222_2222,
    32'h1111_1111
  };

  always @(posedge clk) begin
    cyc <= cyc + 1;
    color = color_e'(cyc % 3);
    `checks(color.name(), names[cyc%3]);
    `checks(getName(2'(cyc % 3)), names[cyc%3]);
    `checkh(getDigit(4'(cyc % 10)), 8'h30 + 8'(cyc % 10));
    sparse = cyc[0] ? HIGH : LOW;
    `checks(sparse.name(), cyc[0] ? "HIGH" : "LOW");
    pkgSparse = cyc[1] ? pkg::HIGH : pkg::LOW;
    `checks(pkgSparse.name(), cyc[1] ? "HIGH" : "LOW");
    `checkh(WIDE[32*(cyc%8)+:32], 32'h1111_1111 * (cyc % 8 + 1));
    `checkh(getWord(3'(cyc + 3)), 32'h1111_1111 * ((cyc + 3) % 8 + 1));
    if (cyc == 20) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
