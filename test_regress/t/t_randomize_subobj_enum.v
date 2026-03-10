// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Check that an enum value is one of the valid members
`define check_enum_color(gotv) \
  if ((gotv) !== RED && (gotv) !== GREEN && (gotv) !== BLUE) begin \
    $write("%%Error: %s:%0d: invalid color=%0d\n", `__FILE__, `__LINE__, (gotv)); \
    `stop; \
  end

`define check_enum_state(gotv) \
  if ((gotv) !== IDLE && (gotv) !== RUN && (gotv) !== STOP) begin \
    $write("%%Error: %s:%0d: invalid state=%0d\n", `__FILE__, `__LINE__, (gotv)); \
    `stop; \
  end

module t;

  typedef enum logic [1:0] {
    RED   = 2'd0,
    GREEN = 2'd1,
    BLUE  = 2'd2
  } color_e;

  typedef enum logic [2:0] {
    IDLE  = 3'd0,
    RUN   = 3'd3,
    STOP  = 3'd5
  } state_e;

  class InnerObj;
    rand color_e color;
    rand state_e state;
  endclass

  class OuterObj;
    rand InnerObj inner;

    function new();
      inner = new();
    endfunction
  endclass

  // Nested: TopObj -> MiddleObj -> InnerObj
  class MiddleObj;
    rand InnerObj inner;

    function new();
      inner = new();
    endfunction
  endclass

  class TopObj;
    rand MiddleObj mid;

    function new();
      mid = new();
    endfunction
  endclass

  initial begin
    OuterObj obj;
    TopObj top;
    obj = new();
    top = new();

    // Test direct sub-object enum (one level deep)
    repeat (20) begin
      `checkd(obj.randomize(), 1)
      `check_enum_color(obj.inner.color)
      `check_enum_state(obj.inner.state)
    end

    // Test nested sub-object enum (two levels deep)
    repeat (20) begin
      `checkd(top.randomize(), 1)
      `check_enum_color(top.mid.inner.color)
      `check_enum_state(top.mid.inner.state)
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
