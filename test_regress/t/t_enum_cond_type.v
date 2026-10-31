// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

package mode_pkg;
  typedef bit [6:0] mode_bits_t;
  typedef enum mode_bits_t { MODE_A = 1, MODE_B = 3, MODE_C = 7 } mode_t;
endpackage

module enum_leaf #(
  parameter mode_pkg::mode_t MODE = mode_pkg::MODE_A,
  parameter mode_pkg::mode_t EXPECTED = mode_pkg::MODE_A
) ();
  initial begin
    `checkd(MODE, EXPECTED);
  end
endmodule

module t (clk);
  input clk;
  import mode_pkg::*;
  typedef mode_t alias_t;
  integer cycle = 0;
  logic [1:0] select;
  bit [1:0] select_bit;
  alias_t value;
  alias_t nested_true;
  alias_t nested_false;
  alias_t mixed;

  for (genvar i = 0; i < 3; ++i) begin : gen_leaf
    localparam logic [1:0] SELECT = 2'(i);
    localparam mode_t EXPECTED = i == 0 ? MODE_A : i == 1 ? MODE_B : MODE_C;
    enum_leaf #(.MODE(SELECT == 1 ? MODE_B : MODE_A),
                .EXPECTED(i == 1 ? MODE_B : MODE_A)) simple_leaf ();
    enum_leaf #(.MODE(SELECT == 0 ? MODE_A : SELECT == 1 ? MODE_B : MODE_C),
                .EXPECTED(EXPECTED)) nested_leaf ();
  end

  function automatic alias_t choose(input alias_t selected);
    return selected;
  endfunction

  always_comb begin
    select = 2'(cycle % 3);
    select_bit = select;
    value = select == 1 ? MODE_B : MODE_A;
    nested_false = select == 0 ? MODE_A : select == 1 ? MODE_B : MODE_C;
    nested_true = select != 2 ? (select == 0 ? MODE_A : MODE_B) : MODE_C;
    mixed = select_bit == 0 ? MODE_A : select == 1 ? MODE_B : MODE_C;
  end

  always @(posedge clk) begin
    `checkd(value, select == 1 ? 3 : 1);
    `checkd(nested_false, select == 0 ? 1 : select == 1 ? 3 : 7);
    `checkd(nested_true, nested_false);
    `checkd(mixed, nested_false);
    `checkd(choose(select == 0 ? MODE_A : select == 1 ? MODE_B : MODE_C), nested_false);
    cycle <= cycle + 1;
    if (cycle == 8) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
