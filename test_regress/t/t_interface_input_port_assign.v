// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Driving interface net-type input ports from the instantiating scope is
// legal via both continuous assignment and port connection when port kind
// defaults to net (IEEE 1800-2023 23.2.2.3, 23.3.3.3). Likewise for net-type
// input ports driven by port connections of a bind instance.

// Scenario: bare input (defaults to net)
interface bare_if (
    input clk
);
  logic data;
endinterface

// Scenario: input with explicit data type (still net for input)
interface logic_if (
    input logic clk
);
  logic data;
endinterface

// Scenario: input with explicit net kind
interface wire_if (
    input wire clk
);
  logic data;
endinterface

module consumer (
    bare_if cif
);
  logic sampled;
  always @(posedge cif.clk) sampled <= cif.data;
endmodule

// Scenario: port connection driving interface input (AstPin path)
interface ifc_status (
    input wire busy
);
endinterface

module dut (
    output logic sleep_o
);
  initial sleep_o = 1'b1;
endmodule

module dut_wrap (
    ifc_status sif
);
  dut u_dut (.sleep_o(sif.busy));
endmodule

// Scenario: bind instance outputs driving the bind target's own input ports,
// as a bind instance is not the target's code (IEEE 1800-2023 23.11)
interface bound_if (
    output logic [6:0] data,
    output logic [6:0] elem
);
endinterface

module bind_target (
    input logic [6:0] data_i,
    input logic [3:1][6:0] elems_i
);
endmodule

interface bind_target_if (
    input logic [6:0] data_i
);
endinterface

// Scenario: bind into a recursive module, reaching every recursion level
interface rec_drv_if (
    input wire [6:0] cnt,
    output logic [6:0] o
);
  assign o = cnt * 7'd11;
endinterface

module bind_rec #(
    parameter int N = 1
) (
    input logic [6:0] cnt_i,
    input logic [6:0] data_i
);
  if (N > 0) begin : g
    bind_rec #(
        .N(N - 1)
    ) sub (
        .cnt_i(cnt_i),
        .data_i()
    );
  end
endmodule

bind bind_rec rec_drv_if u_drv (
    .cnt(cnt_i),
    .o(data_i)
);

module t;
  logic clk = 0;
  always #5 clk = ~clk;
  integer cyc = 0;

  // Continuous assignment scenarios
  bare_if bif (.clk());
  assign bif.clk = clk;
  assign bif.data = 1'b1;

  logic_if lif (.clk());
  assign lif.clk = clk;
  assign lif.data = 1'b1;

  wire_if wif (.clk());
  assign wif.clk = clk;
  assign wif.data = 1'b1;

  consumer cons (.cif(bif));

  // Port connection scenario
  ifc_status sif (.busy());
  dut_wrap u_wrap (.sif(sif));

  // Bind scenarios, into a module, an interface and a recursive module
  bind_target u_target (
      .data_i(),
      .elems_i()
  );
  bind bind_target bound_if u_bound (
      .data(data_i),
      .elem(elems_i[2])
  );
  assign u_target.u_bound.data = 7'(cyc * 3);
  assign u_target.u_bound.elem = 7'(cyc * 5);
  bind_target_if u_target_if (.data_i());
  bind bind_target_if bound_if u_bound (
      .data(data_i),
      .elem()
  );
  assign u_target_if.u_bound.data = 7'(cyc * 7);
  bind_rec u_rec (
      .cnt_i(7'(cyc)),
      .data_i()
  );
  always @(posedge clk) begin
    `checkh(u_target.data_i, 7'(cyc * 3));
    `checkh(u_target.elems_i[2], 7'(cyc * 5));
    `checkh(u_target_if.data_i, 7'(cyc * 7));
    `checkh(u_rec.data_i, 7'(cyc * 11));
    `checkh(u_rec.g.sub.data_i, 7'(cyc * 11));
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 10) begin
      `checkh(bif.clk, clk);
      `checkh(bif.data, 1'b1);
      `checkh(lif.clk, clk);
      `checkh(lif.data, 1'b1);
      `checkh(wif.clk, clk);
      `checkh(wif.data, 1'b1);
      `checkh(sif.busy, 1'b1);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
