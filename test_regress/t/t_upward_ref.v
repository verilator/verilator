// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

// The interface calls an enclosing task or function with the same name as the interface.
interface update;
  task automatic invoke();
    update();
  endtask
endinterface

module update_consumer(update bus);
  task automatic invoke();
    bus.invoke();
  endtask
endmodule

module update_forwarder(update bus);
  update_consumer consumer(.bus(bus));

  task automatic invoke();
    consumer.invoke();
  endtask
endmodule

module task_parent;
  int result = 1;
  update bus();
  update_forwarder forwarder(.bus(bus));

  task automatic update();
    result = result * 2;
  endtask
endmodule

module function_parent;
  int result = 0;
  update bus();
  update_forwarder forwarder(.bus(bus));

  function void update();
    result++;
  endfunction
endmodule

// Parameterized parents give their nested interfaces different return widths.
interface param_getter;
  function automatic int width();
    return $bits(param_value());
  endfunction

  localparam int WIDTH = width();
endinterface

module param_branch #(parameter int W = 8);
  param_getter g();

  function automatic logic [W-1:0] param_value();
    return '0;
  endfunction
endmodule

// A leaf whose last-seen instance is in a pruned generate block resolves in its live context.
module pruned_leaf;
  localparam int W = $bits(pruned_value());

  function automatic int value();
    return int'(pruned_value());
  endfunction
endmodule

module pruned_good #(parameter int W = 8);
  function automatic logic [W-1:0] pruned_value();
    return 1;
  endfunction
  pruned_leaf x();
endmodule

module pruned_parent;
  pruned_good #(8) narrow();
  pruned_good #(16) wide();
  if (0) begin : gone
    pruned_leaf x();
  end
endmodule

// The intermediate module must specialize for the nearer declaration in the generate block.
module const_deep_child;
  class Value;
    localparam int Width = $bits(get_value());

    function automatic int read();
      return get_amount() + int'(get_value());
    endfunction
  endclass

  localparam int W = $bits(get_value());
  localparam int CLASS_W = Value::Width;
  if (W > 8) begin : wide
    localparam int WIDTH = W;
  end

  function automatic int read();
    Value value = new;
    return value.read();
  endfunction
endmodule

module const_deep_mid;
  const_deep_child c();
endmodule

module const_deep_parent;
  function automatic int get_amount();
    return 100;
  endfunction

  function automatic logic [7:0] get_value();
    return 8'd7;
  endfunction

  const_deep_mid m();

  begin : blk
    function automatic logic [15:0] get_value();
      return 16'd19;
    endfunction
    const_deep_mid m();
  end
endmodule

// An explicit import shadows a function re-exported through a wildcard import.
package upward_pkg_a;
  function automatic logic [11:0] upward_pkg_value();
    return '0;
  endfunction
endpackage

package upward_pkg_b;
  import upward_pkg_a::*;
  export upward_pkg_a::*;
endpackage

package upward_pkg_explicit;
  function automatic logic [19:0] upward_pkg_value();
    return '0;
  endfunction
endpackage

module const_import_child;
  localparam int W = $bits(upward_pkg_value());
endmodule

module const_import_parent;
  import upward_pkg_b::*;
  const_import_child c();
  begin : with_explicit_import
    import upward_pkg_b::*;
    import upward_pkg_explicit::upward_pkg_value;
    const_import_child c();
  end
endmodule

module t;
  task_parent task_instance();
  function_parent function_instance();
  param_branch #(8) param_default();
  param_branch #(16) param_override();
  pruned_parent pruned();
  const_deep_parent const_deep();
  const_import_parent const_import();

  initial begin
    task_instance.forwarder.invoke();
    function_instance.forwarder.invoke();
    `checkd(task_instance.result, 2);
    `checkd(function_instance.result, 1);

    `checkd(param_default.g.width(), 8);
    `checkd(param_override.g.width(), 16);
    `checkd(param_default.g.WIDTH, 8);
    `checkd(param_override.g.WIDTH, 16);

    `checkd(pruned.narrow.x.value(), 1);
    `checkd(pruned.narrow.x.W, 8);
    `checkd(pruned.wide.x.W, 16);

    `checkd(const_deep.m.c.W, 8);
    `checkd(const_deep.m.c.CLASS_W, 8);
    `checkd(const_deep.m.c.read(), 107);
    `checkd(const_deep.blk.m.c.wide.WIDTH, 16);
    `checkd(const_deep.blk.m.c.CLASS_W, 16);
    `checkd(const_deep.blk.m.c.read(), 119);

    `checkd(const_import.c.W, 12);
    `checkd(const_import.with_explicit_import.c.W, 20);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
