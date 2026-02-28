// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Leela Pakanati
// SPDX-License-Identifier: CC0-1.0

// Test modport expressions with nested interfaces

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

interface base_reg_if;
  logic [7:0] wr;
  logic [7:0] rd;
  modport host(output wr, input rd);
  modport dev(input wr, output rd);
endinterface

interface example_reg_if;
  logic [15:0] wr;
  logic [15:0] rd;
  modport host(output wr, input rd);
  modport dev(input wr, output rd);
endinterface

interface app_reg_if;
  base_reg_if base ();
  example_reg_if example ();

  // Use modport expressions to expose nested interface signals
  modport host(
      output .base_wr(base.wr),
      input .base_rd(base.rd),
      output .example_wr(example.wr),
      input .example_rd(example.rd)
  );
  modport dev(
      input .base_wr(base.wr),
      output .base_rd(base.rd),
      input .example_wr(example.wr),
      output .example_rd(example.rd)
  );
endinterface

// Deep nesting test (3 levels)
interface inner_if;
  logic [7:0] data;
  modport producer(output data);
  modport consumer(input data);
endinterface

interface middle_if;
  inner_if inner ();
endinterface

interface outer_if;
  middle_if middle ();

  // 3-level deep modport expression
  modport mp(output .deep_out(middle.inner.data), input .deep_in(middle.inner.data));
endinterface

module deep_consumer (
    outer_if.mp port
);
  assign port.deep_out = 8'hDE;
  // Verify reading through deep_in virtual port
  wire [7:0] deep_in_val = port.deep_in;
endmodule

// 4-level deep nesting test
interface level1_if;
  logic [7:0] val;
endinterface

interface level2_if;
  level1_if l1 ();
endinterface

interface level3_if;
  level2_if l2 ();
endinterface

interface level4_if;
  level3_if l3 ();

  // 4-level deep modport expression
  modport mp(output .deep4_w(l3.l2.l1.val), input .deep4_r(l3.l2.l1.val));
endinterface

module deep4_consumer (
    level4_if.mp port
);
  assign port.deep4_w = 8'h4D;
  wire [7:0] deep4_read = port.deep4_r;
endmodule

module app_consumer (
    app_reg_if.dev i_app_regs
);
  // Access through modport expression virtual ports
  assign i_app_regs.base_rd = i_app_regs.base_wr + 8'h1;
  assign i_app_regs.example_rd = i_app_regs.example_wr + 16'h1;
endmodule

module top;
  app_reg_if app_regs ();
  outer_if outer ();
  level4_if lev4 ();

  app_consumer m_app (.i_app_regs(app_regs));
  deep_consumer m_deep (.port(outer));
  deep4_consumer m_deep4 (.port(lev4));

  initial begin
    app_regs.base.wr = 8'hAB;
    app_regs.example.wr = 16'hCDEF;
    #1;
    `checkh(app_regs.base.rd, 8'hAC);
    `checkh(app_regs.example.rd, 16'hCDF0);
    // Verify 3-level deep nesting
    `checkh(outer.middle.inner.data, 8'hDE);
    `checkh(m_deep.deep_in_val, 8'hDE);
    // Verify 4-level deep nesting
    `checkh(lev4.l3.l2.l1.val, 8'h4D);
    `checkh(m_deep4.deep4_read, 8'h4D);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
