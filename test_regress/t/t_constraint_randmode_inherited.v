// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

typedef enum int {
  FIRST,
  SECOND,
  THIRD
} Kind;

class Base;
  rand Kind kind;

  constraint c_kind { kind inside {FIRST, SECOND, THIRD}; }
endclass

class Intermediate extends Base;
  rand int value;

  constraint c_value { value == 31; }

  function new;
    kind = THIRD;
    kind.rand_mode(0);
  endfunction
endclass

class Derived extends Intermediate;
  rand int extra;

  constraint c_extra { extra == 15; }
endclass

class CombinedModes;
  rand int value;

  constraint c_value { value == 7; }

  function new;
    value = 9;
    value.rand_mode(0);
    c_value.constraint_mode(0);
  endfunction
endclass

module t;
  initial begin
    automatic Intermediate intermediate = new;
    automatic Derived derived = new;
    automatic CombinedModes combined_modes = new;
    automatic int randomize_result;

    `checkd(combined_modes.value, 9)
    `checkd(combined_modes.value.rand_mode(), 0)
    `checkd(combined_modes.c_value.constraint_mode(), 0)
    randomize_result = combined_modes.randomize();
    `checkd(randomize_result, 1)
    `checkd(combined_modes.value, 9)

    `checkd(intermediate.kind, THIRD)
    `checkd(intermediate.kind.rand_mode(), 0)
    `checkd(derived.kind, THIRD)
    `checkd(derived.kind.rand_mode(), 0)

    repeat (20) begin
      randomize_result = intermediate.randomize();
      `checkd(randomize_result, 1)
      `checkd(intermediate.kind, THIRD)
      `checkd(intermediate.kind.rand_mode(), 0)
      `checkd(intermediate.value, 31)
      `checkd(intermediate.value.rand_mode(), 1)

      randomize_result = derived.randomize();
      `checkd(randomize_result, 1)
      `checkd(derived.kind, THIRD)
      `checkd(derived.kind.rand_mode(), 0)
      `checkd(derived.value, 31)
      `checkd(derived.value.rand_mode(), 1)
      `checkd(derived.extra, 15)
      `checkd(derived.extra.rand_mode(), 1)
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
