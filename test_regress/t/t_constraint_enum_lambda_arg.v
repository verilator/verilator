// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Aditya Shevade
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

typedef enum bit [1:0] {
  READ,
  WRITE,
  FLUSH,
  INVALID
} cmd_e;

class EnumLambdaArg;
  rand cmd_e items[8];
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
  rand entry_t items[8];
  constraint c_find {
    // verilator lint_off CONSTRAINTIGN
    items.find(item) with (item.kind == WRITE).size() >= 0;
    // verilator lint_on CONSTRAINTIGN
  }
endclass

// Same shape, but via a locator method (find()) instead of a reduction
// (sum()) -- both take a with (...) lambda body the same way.
class EnumLambdaArgFind;
  rand cmd_e items[8];
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
    int ok;
    repeat (5) begin
      ok = obj.randomize();
      `checkd(ok, 1);
      ok = sobj.randomize();
      `checkd(ok, 1);
      ok = fobj.randomize();
      `checkd(ok, 1);
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
