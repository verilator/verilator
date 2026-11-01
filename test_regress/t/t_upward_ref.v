// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

interface caller_if;
  task automatic invoke();
    update();
  endtask
endinterface

module mul;
  int mul_count = 1;
  caller_if caller();

  task automatic update();
    mul_count = mul_count * 2;
  endtask
endmodule

module add;
  int add_count = 0;
  caller_if caller();

  function void update;
    add_count++;
  endfunction
endmodule

interface bit_getter;
  function automatic int get_bits();
    return $bits(get_value());
  endfunction
endinterface

interface deep_bit_getter;
  function automatic int get_bits();
    return $bits(get_value());
  endfunction
endinterface

interface local_bit_getter;
  function automatic int get_bits();
    return $bits(get_value());
  endfunction
endinterface

interface scoped_bit_getter;
  function automatic int get_bits();
    return $bits(get_value());
  endfunction
endinterface

module first;
  bit_getter getter();
  function automatic logic [7:0] get_value();
    return 8'h87;
  endfunction
endmodule

module second;
  third a();
  fourth b();

  function automatic logic [31:0] get_value();
    return 32'h1234_5678;
  endfunction
endmodule

module third;
  bit_getter getter();
endmodule

module fourth;
  bit_getter getter();

  function automatic logic [63:0] get_value();
    return 64'h1234_5678_1234_5678;
  endfunction
endmodule

module deep_first;
  deep_second second();

  function automatic logic [7:0] get_value();
    return 8'h87;
  endfunction
endmodule

module deep_second;
  deep_third third();

  function automatic logic [31:0] get_value();
    return 32'h1234_5678;
  endfunction
endmodule

module deep_third;
  deep_bit_getter getter();

  function automatic logic [63:0] get_value();
    return 64'h1234_5678_1234_5678;
  endfunction
endmodule

module shared_branch;
  local_bit_getter getter();

  function automatic logic [15:0] get_value();
    return 16'h1234;
  endfunction
endmodule

module wrapper_a;
  shared_branch branch();
endmodule

module wrapper_b;
  shared_branch branch();
endmodule

module scoped_parent;
  if (1) begin : narrow
    scoped_bit_getter getter();

    function automatic logic [6:0] get_value();
      return 7'h12;
    endfunction
  end

  if (1) begin : wide
    scoped_bit_getter getter();

    function automatic logic [64:0] get_value();
      return 65'h1234;
    endfunction
  end
endmodule

function int f(int y);
  return y + 1;
endfunction

package p;
  function void g();
    $display("p::g");
  endfunction
endpackage

module no_upward_ref;
endmodule

module t;
  // Setup for IEEE 1800-2023 23.8.1 Example 2, with 'f' renamed to 'g' to avoid collisions.
  import p::*;
  if (1) begin : b
    bit g_called;
    function void call_g();
      g();
    endfunction
    function void g();
      g_called = 1;
      $display("top.b.g");
    endfunction
  end

  mul mul();
  add add();

  first first();
  first first_same();
  second second();
  deep_first deep();
  wrapper_a wrapper_a();
  wrapper_b wrapper_b();
  scoped_parent scoped();
  no_upward_ref no_up_ref();

  initial begin
    int x;

    // IEEE 1800-2023 23.8.1 Example 2: The unqualified call in b.call_g resolves to b.g.
    b.call_g();
    `checkd(b.g_called, 1);

    // IEEE 1800-2023 23.8.1 Example 1: The unqualified call resolves to compilation-unit f.
    x = f(1);
    `checkd(x, 2);

    // Upward referencing should connect references
    // to tasks/functions in relevant instance hierarchy.
    mul.caller.invoke();
    `checkd(mul.mul_count, 2);
    add.caller.invoke();
    `checkd(add.add_count, 1);

    // Upward referenced function should have correct return type.
    `checkd(first.getter.get_bits(), 8);
    `checkd(first_same.getter.get_bits(), 8);
    `checkd(second.a.getter.get_bits(), 32);
    `checkd(second.b.getter.get_bits(), 64);
    `checkd(deep.second.third.getter.get_bits(), 64);
    `checkd(wrapper_a.branch.getter.get_bits(), 16);
    `checkd(wrapper_b.branch.getter.get_bits(), 16);
    `checkd(scoped.narrow.getter.get_bits(), 7);
    `checkd(scoped.wide.getter.get_bits(), 65);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
