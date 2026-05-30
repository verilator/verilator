// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define STRINGIFY(x) `"x`"

/* verilator lint_off MULTITOP */

`ifdef TRACE_DUMPVARS_CASE_HIER_STRUCT
`define TRACE_DUMPVARS_PACKED_STRUCT_BRANCH
`elsif TRACE_DUMPVARS_CASE_CPPTOP_HIER_STRUCT
`define TRACE_DUMPVARS_PACKED_STRUCT_BRANCH
`elsif TRACE_DUMPVARS_CASE_CPPTOP_HIER_STRUCT2
`define TRACE_DUMPVARS_PACKED_STRUCT_BRANCH
`endif

`ifdef TRACE_DUMPVARS_CASE_HIER_ARRAY
`define TRACE_DUMPVARS_ARRAY_BRANCH
`elsif TRACE_DUMPVARS_CASE_HIER_ARRAY_OOB
`define TRACE_DUMPVARS_ARRAY_BRANCH
`elsif TRACE_DUMPVARS_CASE_CPPTOP_HIER_ARRAY
`define TRACE_DUMPVARS_ARRAY_BRANCH
`elsif TRACE_DUMPVARS_CASE_CPPTOP_HIER_ARRAY_OOB
`define TRACE_DUMPVARS_ARRAY_BRANCH
`endif

`ifdef TRACE_DUMPVARS_CASE_FUNC
`define TRACE_DUMPVARS_TASK_BRANCH
`elsif TRACE_DUMPVARS_CASE_TASK
`define TRACE_DUMPVARS_TASK_BRANCH
`elsif TRACE_DUMPVARS_CASE_TASK2
`define TRACE_DUMPVARS_TASK_BRANCH
`endif

`ifdef TRACE_DUMPVARS_PACKED_STRUCT_BRANCH
typedef struct packed {
  logic [31:0] add;
  logic [31:0] cyc;
  logic [31:0] inner;
} deep_t;

typedef struct packed {
  deep_t deep;
  logic [31:0] value;
} top_t;
`endif

`ifdef TRACE_DUMPVARS_TASK_BRANCH
function int get_trace_level;
  return 1;
endfunction

function void varsdump;
  $dumpvars(get_trace_level());
endfunction

`ifdef TRACE_DUMPVARS_CASE_FUNC
function void setup_trace;
  $dumpfile(`STRINGIFY(`TEST_DUMPFILE));
  varsdump();
endfunction
`else
task setup_trace;
  $dumpfile(`STRINGIFY(`TEST_DUMPFILE));
  varsdump();
endtask
`endif

`ifdef TRACE_DUMPVARS_CASE_TASK2
task setup_trace_nested;
  setup_trace();
endtask
`endif
`endif

module t
`ifdef TRACE_DUMPVARS_CASE_ADD_MODULE
;
`else
(
    input clk
);
`endif
  int cyc;
`ifdef TRACE_DUMPVARS_CASE_ADD_MODULE
  logic clk;
`endif
`ifdef TRACE_DUMPVARS_CASE_CONTEXT
  int top;
`endif
`ifdef TRACE_DUMPVARS_CASE_WIRE
  int counter;
`endif
`ifdef TRACE_DUMPVARS_PACKED_STRUCT_BRANCH
  top_t mystruct;
`endif
`ifdef TRACE_DUMPVARS_CASE_STRUCT
  typedef struct packed {
    logic [7:0] \x ;
    logic [7:0] y;
  } point_t;

  typedef struct packed {
    point_t origin;
    point_t size;
  } rect_t;

  rect_t rect;
  point_t \pt ;
`endif

`ifdef TRACE_DUMPVARS_ARRAY_BRANCH
  sub #(10) arr[2](.*);
`elsif TRACE_DUMPVARS_CASE_GEN
  genvar i;
  generate
    for (i = 0; i < 2; i = i + 1) begin : gen_sub
      sub #(10 * (i + 1)) sub_i(.*);
    end
  endgenerate
`elsif TRACE_DUMPVARS_PACKED_STRUCT_BRANCH
`elsif TRACE_DUMPVARS_CASE_STRUCT
  sub #(10) sub_a(.*);
`else
  sub #(10) sub_a(.*);
  sub #(20) sub_b(.*);
`endif

`ifdef TRACE_DUMPVARS_CASE_ADD_MODULE
  initial begin
    clk = 0;
    forever #1 clk = !clk;
  end
`endif

  always @(posedge clk) begin
    cyc <= cyc + 1;
`ifdef TRACE_DUMPVARS_CASE_STRUCT
    \pt .\x  <= \pt .\x  + 1;
    \pt .y <= \pt .y + 2;
    rect.origin.\x  <= rect.origin.\x  + 1;
    rect.origin.y <= rect.origin.y + 2;
    rect.size.\x  <= 8'd100;
    rect.size.y <= 8'd200;
`endif
`ifdef TRACE_DUMPVARS_CASE_WIRE
    counter <= counter + 2;
`endif
`ifdef TRACE_DUMPVARS_CASE_ADD_MODULE
    if (cyc == 1) begin
      $dumpfile({`STRINGIFY(`TEST_OBJ_DIR), "/simx1.vcd"});
      $dumpvars(0, sub_b);
    end
`endif
    if (cyc == 5) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

`ifdef TRACE_DUMPVARS_CASE_ADD_MODULE
  initial begin
    $dumpfile({`STRINGIFY(`TEST_OBJ_DIR), "/simx0.vcd"});
    $dumpvars(1, sub_a);
  end
`elsif TRACE_DUMPVARS_CASE_STRUCT
  initial begin
    $dumpfile(`STRINGIFY(`TEST_DUMPFILE));
    $dumpvars(1, rect.origin.\x );
    $dumpvars(1, \pt .\y );
  end
`elsif TRACE_DUMPVARS_PACKED_STRUCT_BRANCH
  initial begin
    $dumpfile(`STRINGIFY(`TEST_DUMPFILE));
`ifdef TRACE_DUMPVARS_CASE_HIER_STRUCT
    $dumpvars(1, t.mystruct.deep);
`elsif TRACE_DUMPVARS_CASE_CPPTOP_HIER_STRUCT
    $dumpvars(1, cpptop.t.mystruct.deep);
`elsif TRACE_DUMPVARS_CASE_CPPTOP_HIER_STRUCT2
    $dumpvars(1, cpptop.t.mystruct.deep.inner);
`else
`error "Missing packed struct trace_dumpvars case"
`endif
  end

  always_comb begin
    mystruct.value = cyc + 32'd10;
    mystruct.deep.add = 32'd11;
    mystruct.deep.cyc = cyc;
    mystruct.deep.inner = cyc + mystruct.deep.add;
  end
`elsif TRACE_DUMPVARS_ARRAY_BRANCH
  initial begin
    $dumpfile(`STRINGIFY(`TEST_DUMPFILE));
`ifdef TRACE_DUMPVARS_CASE_HIER_ARRAY
    $dumpvars(1, t.arr[1].deep);
`elsif TRACE_DUMPVARS_CASE_HIER_ARRAY_OOB
    $dumpvars(1, t.arr[999].deep);
`elsif TRACE_DUMPVARS_CASE_CPPTOP_HIER_ARRAY
    $dumpvars(1, cpptop.t.arr[1].deep);
`elsif TRACE_DUMPVARS_CASE_CPPTOP_HIER_ARRAY_OOB
    $dumpvars(1, cpptop.t.arr[999].deep);
`else
`error "Missing array trace_dumpvars case"
`endif
  end
`elsif TRACE_DUMPVARS_CASE_GEN
  initial begin
    $dumpfile(`STRINGIFY(`TEST_DUMPFILE));
    $dumpvars(0, gen_sub[0]);
  end
`elsif TRACE_DUMPVARS_TASK_BRANCH
`elsif TRACE_DUMPVARS_CASE_HIER_GLOBAL
`elsif TRACE_DUMPVARS_CASE_HIER_GLOBAL_TASK
`elsif TRACE_DUMPVARS_CASE_NONCONST_SCOPE
  initial begin: dumpblock
    int level;
    if (!$value$plusargs("LEVEL=%d", level)) level = 0;
    $dumpfile(`STRINGIFY(`TEST_DUMPFILE));
    $dumpvars(level, t.sub_a);
  end
`elsif TRACE_DUMPVARS_CASE_SUB
  initial begin
    $dumpfile(`STRINGIFY(`TEST_DUMPFILE));
  end
`elsif TRACE_DUMPVARS_CASE_SUB0
  initial begin
    $dumpfile(`STRINGIFY(`TEST_DUMPFILE));
  end
`else
  initial begin
    $dumpfile(`STRINGIFY(`TEST_DUMPFILE));
`ifdef TRACE_DUMPVARS_CASE_BASE
    $dumpvars(0);
`elsif TRACE_DUMPVARS_CASE_SCOPE
    $dumpvars(0, sub_a);
`elsif TRACE_DUMPVARS_CASE_MULTI_SCOPE
    $dumpvars(0+1, t, t.sub_a.deep_i);
`elsif TRACE_DUMPVARS_CASE_ABS_SCOPE
    $dumpvars(0, t.sub_a);
`elsif TRACE_DUMPVARS_CASE_OVERRIDE
    $dumpvars(1, t.sub_a.deep_i);
    $dumpvars(0);
`elsif TRACE_DUMPVARS_CASE_CONTEXT
    $dumpvars(1, t.sub_a.deep_i);
    $dumpvars(0, top);
`elsif TRACE_DUMPVARS_CASE_LEVEL
    $dumpvars(1);
`elsif TRACE_DUMPVARS_CASE_LEVEL_SCOPE
    $dumpvars(1, sub_a);
`elsif TRACE_DUMPVARS_CASE_HIER_SCOPE
    $dumpvars(1, sub_a.deep_i);
`elsif TRACE_DUMPVARS_CASE_WIRE
    $dumpvars(0, cyc, counter);
`elsif TRACE_DUMPVARS_CASE_T
    $dumpvars(t);
`elsif TRACE_DUMPVARS_CASE_MISSING_SCOPE
    $dumpvars(0, missing_module);
`elsif TRACE_DUMPVARS_CASE_MISSING2
    $dumpvars(t.missingname);
`elsif TRACE_DUMPVARS_CASE_MISSING3
    $dumpvars(0, t.missing);
`elsif TRACE_DUMPVARS_CASE_MISSING4
    $dumpvars(0, t.sub_a.missing);
`elsif TRACE_DUMPVARS_CASE_MISSING5
    $dumpvars(0, missing.child);
`elsif TRACE_DUMPVARS_CASE_CPPTOP
    $dumpvars(0, cpptop, cpptop.t);
`elsif TRACE_DUMPVARS_CASE_CPPTOP2
    $dumpvars(0, cpptop, cpptop.notfound);
`elsif TRACE_DUMPVARS_CASE_CPPTOP_MISSING
    $dumpvars(0, missing_module);
`elsif TRACE_DUMPVARS_CASE_CPPTOP_MISSING2
    $dumpvars(t.missingname);
`elsif TRACE_DUMPVARS_CASE_CPPTOP_MISSING3
    $dumpvars(0, t.missing);
`elsif TRACE_DUMPVARS_CASE_CPPTOP_MISSING4
    $dumpvars(0, t.sub_a.missing);
`else
`error "Missing trace_dumpvars case define"
`endif
  end
`endif
endmodule

module sub #(
  parameter int ADD = 0
)(
    input int cyc
);
  int value;
  always_comb value = cyc + ADD;

`ifdef TRACE_DUMPVARS_CASE_HIER_GLOBAL_TASK
  function void dump_from_func;
    $dumpvars(1, t);
  endfunction

  task setup_trace;
    $dumpfile(`STRINGIFY(`TEST_DUMPFILE));
    dump_from_func();
  endtask
`endif

`ifdef TRACE_DUMPVARS_ARRAY_BRANCH
  deep #(ADD + 1) deep(.*);
`elsif TRACE_DUMPVARS_CASE_BASE
`elsif TRACE_DUMPVARS_CASE_WIRE
`elsif TRACE_DUMPVARS_CASE_CPPTOP
`elsif TRACE_DUMPVARS_CASE_CPPTOP2
`elsif TRACE_DUMPVARS_CASE_STRUCT
`else
  deep #(ADD + 1) deep_i(.*);
`endif

`ifdef TRACE_DUMPVARS_CASE_HIER_GLOBAL
  initial begin
    $dumpfile(`STRINGIFY(`TEST_DUMPFILE));
    $dumpvars(1, t);
  end
`elsif TRACE_DUMPVARS_CASE_HIER_GLOBAL_TASK
  initial begin
    setup_trace();
  end
`elsif TRACE_DUMPVARS_CASE_TASK2
  initial begin
    setup_trace_nested;
  end
`elsif TRACE_DUMPVARS_TASK_BRANCH
  initial begin
    setup_trace;
  end
`elsif TRACE_DUMPVARS_CASE_SUB
  initial begin
    $dumpvars(1);
  end
`elsif TRACE_DUMPVARS_CASE_SUB0
  initial begin
    $dumpvars(0);
  end
`endif
endmodule

module deep #(
  parameter int ADD = 0
)(
    input int cyc
);
  int inner;
`ifdef TRACE_DUMPVARS_CASE_HIER_GLOBAL
  int t;
`elsif TRACE_DUMPVARS_CASE_HIER_GLOBAL_TASK
  int t;
`endif
  always_comb inner = cyc + ADD;

`ifdef TRACE_DUMPVARS_CASE_HIER_GLOBAL_TASK
  function void dump_from_func;
    $dumpvars(1, t);
  endfunction

  task setup_trace;
    $dumpfile(`STRINGIFY(`TEST_DUMPFILE));
    dump_from_func();
  endtask

  initial begin
    setup_trace();
  end
`elsif TRACE_DUMPVARS_CASE_HIER_GLOBAL
  initial begin
    $dumpfile(`STRINGIFY(`TEST_DUMPFILE));
    $dumpvars(1, t);
  end
`elsif TRACE_DUMPVARS_CASE_CONTEXT
  initial begin
    $dumpvars(0);
  end
`endif
endmodule

/* verilator lint_on MULTITOP */
