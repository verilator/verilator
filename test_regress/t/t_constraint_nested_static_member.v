// DESCRIPTION: Verilator: Static class properties in nested constraints
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

class base;
  static int limit;

  static function int get_limit();
    return limit + 1;
  endfunction
endclass

class child extends base;
  rand int value;
  rand int function_value;
  constraint selected {value == base::limit;}
  constraint selected_function {function_value == base::get_limit();}
endclass

class group_t;
  rand child item = new;
  constraint nonnegative {item.value <= 100;}
endclass

// Test: static rand members of a rand member, constrained in their class and through the handle
class static_cfg;
  static rand bit g;
  static rand bit h;
  constraint c {g == 1;}
endclass

class static_cfg_holder;
  rand static_cfg s;
  constraint c {s.h == 1;}
  function new();
    s = new;
  endfunction
endclass

// Test: static rand member reached through two levels of rand members
class chain_leaf;
  static rand bit [4:0] v;
  constraint c {v < 9;}
endclass

class chain_mid;
  rand chain_leaf l;
  function new();
    l = new;
  endfunction
endclass

class chain_top;
  rand chain_mid m;
  constraint c {m.l.v > 6;}
  function new();
    m = new;
  endfunction
endclass

// Test: static rand member of a rand member in an inline constraint, with rand_mode used
class inline_cfg;
  static rand bit [3:0] g;
  rand bit [3:0] m;
endclass

class inline_cfg_holder;
  rand inline_cfg s;
  rand bit [3:0] y;
  function new();
    s = new;
  endfunction
endclass

// Test: static rand member of a rand member whose class is also randomized directly
class order_cfg;
  static rand bit [3:0] h;
  constraint c {h < 8;}
endclass

class order_cfg_holder;
  rand order_cfg s;
  constraint c {s.h == 3;}
  function new();
    s = new;
  endfunction
endclass

// Test: static rand member of a rand member whose class is a sibling of the holder
class sibling_root;
endclass

class sibling_cfg extends sibling_root;
  static rand bit [3:0] g;
  constraint c {g < 10;}
endclass

class sibling_holder extends sibling_root;
  rand sibling_cfg cfg;
  rand bit [3:0] y;
  constraint c {y == cfg.g;}
  function new();
    cfg = new;
  endfunction
endclass

// Test: a static rand member constrained through a rand handle stays random in its own class
typedef class own_cfg_base;
typedef class own_cfg_derived;
class own_cfg_holder;
  rand own_cfg_derived s;
  constraint c {s.g == 3;}
  function new();
    s = new;
  endfunction
endclass

class own_cfg_base;
  static rand bit [3:0] g;
endclass

class own_cfg_derived extends own_cfg_base;
endclass

module t;
  initial begin
    group_t g;
    int randomize_result;
    g = new;
    for (int i = 1; i < 3; i++) begin
      base::limit = i * 17;
      randomize_result = g.randomize();
      `checkd(randomize_result, 1);
      `checkd(g.item.value, base::limit);
      `checkd(g.item.function_value, base::limit + 1);
    end

    begin
      automatic static_cfg_holder sh = new;
      automatic int ok;
      repeat (20) begin
        ok = sh.randomize();
        `checkd(ok, 1);
        `checkd(static_cfg::g, 1);
        `checkd(static_cfg::h, 1);
      end
    end

    begin
      automatic chain_top ct = new;
      automatic int ok;
      repeat (20) begin
        ok = ct.randomize();
        `checkd(ok, 1);
        `checkd(chain_leaf::v > 6 && chain_leaf::v < 9, 1);
      end
    end

    begin
      automatic inline_cfg_holder ih = new;
      automatic int ok;
      ih.s.m.rand_mode(1);
      ih.s.g.rand_mode(1);
      ok = ih.randomize() with {y == s.g;};
      `checkd(ok, 1);
    end

    begin
      automatic order_cfg oc = new;
      automatic order_cfg_holder oh = new;
      automatic int ok;
      ok = oc.randomize();
      `checkd(ok, 1);
      `checkd(order_cfg::h < 8, 1);
      repeat (20) begin
        ok = oh.randomize();
        `checkd(ok, 1);
        `checkd(order_cfg::h, 3);
      end
    end

    begin
      automatic sibling_holder sb = new;
      automatic int ok;
      repeat (20) begin
        ok = sb.randomize();
        `checkd(ok, 1);
        `checkd(sibling_cfg::g < 10, 1);
        `checkd(sb.y, sibling_cfg::g);
      end
    end

    begin
      automatic own_cfg_holder oh = new;
      automatic own_cfg_base ob = new;
      automatic int ok;
      automatic bit changed = 0;
      ok = oh.randomize();
      `checkd(ok, 1);
      `checkd(own_cfg_base::g, 3);
      repeat (20) begin
        ok = ob.randomize();
        `checkd(ok, 1);
        if (own_cfg_base::g != 3) changed = 1;
      end
      `checkd(changed, 1);
    end

    $display("*-* All Finished *-*");
    $finish;
  end
endmodule
