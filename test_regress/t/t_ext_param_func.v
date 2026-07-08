// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);

function automatic int align(input int a, input int b);
  return a - (a % b);
endfunction

class Foo;

  static function int mul(input int a, input int b);
    return a * b;
  endfunction

endclass

class FooParam #(parameter int param = 5);

  static function int mul(input int a);
    return a * param;
  endfunction

endclass

class Base #(parameter int param = 5);

  function int get_base_param();
    return param;
  endfunction

  static function int alignUp(input int a);
    return ((a + param - 1) / param) * param;
  endfunction

endclass

class Derived #(
  parameter int a = 17,
  parameter int b = 8,
  parameter int c = align(a, b),
  parameter int d = Base#(b)::alignUp(a),
  parameter int e = Foo::mul(a, b),
  parameter int f = FooParam#()::mul(a)
) extends Base #(
  .param (a)
);

  function int get_third_param();
    return c;
  endfunction

  function int get_fourth_param();
    return d;
  endfunction

  function int get_fifth_param();
    return e;
  endfunction

  function int get_sixth_param();
    return f;
  endfunction

endclass

module t (clk);
  input clk;

  Derived inst = new;

  always @(posedge clk) begin
    `checkh(inst.get_base_param(), 17)
    `checkh(inst.get_third_param(), 16)
    `checkh(inst.get_fourth_param(), 24)
    `checkh(inst.get_fifth_param(), 136)
    `checkh(inst.get_sixth_param(), 85)
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
