// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// verilator lint_off MULTIDRIVEN

interface ifc;
  // Tristate net resolved across an inout port connected hierarchically to
  // this interface signal (iface.data <-> dut inout port).
  wire [7:0] data;
endinterface

module dut (
    inout wire [7:0] data,
    input bit oe,
    input logic [7:0] val
);
  // The inout port drives the interface net when enabled, releases it (Z) otherwise.
  assign data = oe ? val : 8'hzz;
endmodule

module t;
  ifc ifc0 ();
  bit oe, top_oe;
  logic [7:0] val, topval;

  // A second driver from the top, so resolution is observable from both sides.
  assign ifc0.data = top_oe ? topval : 8'hzz;

  dut u (
      .data(ifc0.data),
      .oe(oe),
      .val(val)
  );

  initial begin
    // dut drives the interface net through the inout port.
    oe = 1;
    val = 8'hA5;
    top_oe = 0;
    topval = 8'h00;
    #1 `checkh(ifc0.data, 8'hA5);
    // top drives, dut releases.
    oe = 0;
    top_oe = 1;
    topval = 8'h3C;
    #1 `checkh(ifc0.data, 8'h3C);
    // Neither drives: net floats to Z.
    oe = 0;
    top_oe = 0;
    #1 `checkh(ifc0.data, 8'hzz);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
