// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

typedef class Cls;

class Base;
  class BaseInner;
    int value = 10;
    function void test;
      if (value != 10) $stop;
      if (this.value != 10) $stop;
      value = 20;
      if (value != 20) $stop;
      this.value = 30;
      if (value != 30) $stop;
    endfunction
  endclass

  int value = 1;
  BaseInner inner = new;
  function void test;
    if (value != 1) $stop;
    if (this.value != 1) $stop;
    value = 2;
    if (value != 2) $stop;
    this.value = 3;
    if (value != 3) $stop;
  endfunction
endclass

class Cls extends Base;
  class BaseInner extends Base::BaseInner;
    int value = 100;
    function void test;
      if (value != 100) $stop;
      if (this.value != 100) $stop;
      if (super.value != 10) $stop;
      super.test();
      if (value != 100) $stop;
      if (this.value != 100) $stop;
      if (super.value != 30) $stop;
      value = 200;
      if (value != 200) $stop;
      this.value = 300;
      if (value != 300) $stop;
    endfunction
  endclass

  int value = 20;
  BaseInner inner = new;
  function void test;
    if (value != 20) $stop;
    if (this.value != 20) $stop;
    if (super.value != 1) $stop;

    super.test();
    if (this.value != 20) $stop;

    super.value = 9;
    this.value = 29;
    if (super.value != 9) $stop;
    if (value != 29) $stop;

    inner.test();
  endfunction
endclass

class ItemHolder #(
    type P = Base
) extends P;
  Base item;
  integer x;
endclass

// Note: shadowing occurs for implicit parameterized extends (without `#()`)
class LocalHolder extends ItemHolder;
  function Cls get();
    Cls item;
    int ok;
    ok = $cast(item, this.item);
    `checkd(ok, 1);
    return item;
  endfunction
  function void set_shadowing(integer x);
    // IEEE 1800-2023 8.11's own example: the argument shadows the property, and
    // this.x is how the property is reached.
    this.x = x;
  endfunction
  task read_back_shadowing();
    `checkd(this.x, 42);
    `checkd(super.x, 42);
  endtask
endclass

module t;
  initial begin
    Cls c;
    LocalHolder holder;
    c = new;
    c.test();
    holder = new;
    holder.item = c;
    `checkd(holder.get() == c, 1);
    holder.set_shadowing(42);
    holder.read_back_shadowing();
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
