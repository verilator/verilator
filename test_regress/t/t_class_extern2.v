// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

class One #(
    type VALUE_T = int unsigned
);
  typedef One#(VALUE_T) self_t;
  VALUE_T value;
  extern static function self_t create(VALUE_T value);
endclass

class Two #(
    type VALUE_T = int unsigned
);
  VALUE_T value;
  extern static function Two#(VALUE_T) create(VALUE_T value);
`ifdef NEVER
  // works ok if put function directly here
  static function Two#(VALUE_T) create(VALUE_T value);
    Two #(VALUE_T) obj = new();
    obj.value = value;
    return obj;
  endfunction
`endif
endclass

function One::self_t One::create(VALUE_T value);
  One #(VALUE_T) obj = new();
  obj.value = value;
  return obj;
endfunction

function Two#(Two::VALUE_T) Two::create(VALUE_T value);
  Two #(VALUE_T) obj = new();
  obj.value = value;
  return obj;
endfunction

module t;
  initial begin
    One #(string) one;
    Two #(string) two;
    one = One#(string)::create("one");
    two = Two#(string)::create("two");
    if (one.value !== "one") $stop;
    if (two.value !== "two") $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
