// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%p exp=%p\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

`define check_rand(cl, field, constr, cond) \
begin \
  automatic longint prev_result; \
  automatic int ok; \
  if (!bit'(cl.randomize() with { constr; })) $stop; \
  prev_result = longint'(field); \
  if (!(cond)) $stop; \
  repeat(9) begin \
    longint result; \
    if (!bit'(cl.randomize() with { constr; })) $stop; \
    result = longint'(field); \
    if (!(cond)) $stop; \
    if (result != prev_result) ok = 1; \
    prev_result = result; \
  end \
  if (ok != 1) $stop; \
end

class Cls #(
    int LIMIT = 3
);
  rand int x;
  int y = -100;
  constraint x_limit {x <= LIMIT;}
  ;
endclass

class ParamBase #(type T = int);
  rand bit [7:0] f;
  rand bit [14:0] inherited_only;
  rand T typed_value;
endclass

class ParamDerived extends ParamBase #(bit [32:0]);
  rand bit [6:0] own_value;
endclass

class ParamGrandchild extends ParamDerived;
endclass

class BitDerived extends ParamBase #(bit);
endclass

typedef ParamGrandchild param_alias_t;

module t;
  initial begin
    automatic Cls #() cd = new;
    automatic Cls #(5) c5 = new;
    automatic ParamDerived derived = new;
    automatic param_alias_t grandchild = new;
    automatic BitDerived bit_derived = new;
    bit [7:0] f;
    bit [6:0] own_value;
    bit [32:0] typed_value;

    `check_rand(cd, cd.x, x > 0, cd.x > 0 && cd.x <= 3);
    `check_rand(cd, cd.x, x > y, cd.x > -100 && cd.x <= 3);
    if (cd.randomize() with {x > 3;} == 1) $stop;

    `check_rand(c5, c5.x, x > 0, c5.x > 0 && c5.x <= 5);
    `check_rand(c5, c5.x, x > y, c5.x > -100 && c5.x <= 5);
    if (c5.randomize() with {x >= 5;} == 0) $stop;
    if (c5.x != 5) $stop;

    for (int i = 0; i < 20; ++i) begin
      f = 8'(i + 8'h42);
      own_value = 7'(i + 7'h21);
      typed_value = 33'h1_0000_0000 + 33'(i);
      `checkh(derived.randomize() with {
        f == local::f;
        own_value == local::own_value;
        typed_value == local::typed_value;
        inherited_only == 15'(local::f);
      }, 1)
      `checkh(derived.f, f)
      `checkh(derived.own_value, own_value)
      `checkh(derived.typed_value, typed_value)
      `checkh(derived.inherited_only, 15'(f))
      `checkh(grandchild.randomize() with { f == local::f; }, 1)
      `checkh(grandchild.f, f)
      `checkh(bit_derived.randomize() with { f == local::f; }, 1)
      `checkh(bit_derived.f, f)
      `checkh(derived.randomize() with (f) { f == local::f; }, 1)
      `checkh(derived.f, f)
      `checkh(derived.randomize() with { this.f == local::f; }, 1)
      `checkh(derived.f, f)
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
