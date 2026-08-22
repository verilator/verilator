// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Aditya Shevade
// SPDX-License-Identifier: CC0-1.0

typedef enum bit [1:0] {
  READ,
  WRITE,
  FLUSH,
  INVALID
} cmd_e;

class EnumLambdaArg;
  rand cmd_e items[];
  constraint c_size {
    items.size() == 8;
  }
  constraint c_count {
    items.sum() with (item == WRITE ? 1 : 0) == 3;
  }
endclass

// Same shape, but the enum lives in a struct field reached via the lambda
// argument (item.kind), not the array element itself.
typedef struct {
  cmd_e kind;
} entry_t;
class StructFieldEnumLambdaArg;
  rand entry_t items[];
  constraint c_size {
    items.size() == 8;
  }
  constraint c_count {
    items.sum() with (item.kind == WRITE ? 1 : 0) == 3;
  }
endclass

// Same shape, but via a locator method (find()) instead of a reduction
// (sum()) -- both take a with (...) lambda body the same way.
class EnumLambdaArgFind;
  rand cmd_e items[];
  constraint c_size {
    items.size() == 8;
  }
  constraint c_find {
    // find() with (...) inside a constraint is separately unsupported
    // (CONSTRAINTIGN, fatal by default) -- suppressed here since this
    // test is only about the enum literal not crashing the compiler.
    // verilator lint_off CONSTRAINTIGN
    items.find(item) with (item == WRITE).size() >= 0;
    // verilator lint_on CONSTRAINTIGN
  }
endclass

module t;
  initial begin
    automatic EnumLambdaArg obj = new();
    automatic StructFieldEnumLambdaArg sobj = new();
    automatic EnumLambdaArgFind fobj = new();
    repeat (5) void'(obj.randomize());
    repeat (5) void'(sobj.randomize());
    repeat (5) void'(fobj.randomize());

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
