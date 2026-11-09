// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Sequences, properties and signals referenced hierarchically in an interface and a module
// that are specialized by parameters

interface bus_if #(
    parameter int W = 1
);
  logic valid = 1'b0;
  logic [W-1:0] data = '0;

  sequence s_valid(logic v);
    v == 1'b1;
  endsequence

  property p_data(logic v, logic [W-1:0] d);
    v |-> d != '0;
  endproperty
endinterface

module sub #(
    parameter int W = 1
);
  property p_true;
    1'b1;
  endproperty
endmodule

module t (
    input clk
);
  int cyc = 0;

  bus_if #(.W(8)) bus ();
  sub #(.W(2)) u_sub ();

  // Local sequence with a hierarchical argument
  sequence s_local(logic v);
    v == 1'b1;
  endsequence
  int local_hits = 0;
  cover property (@(posedge clk) s_local(bus.valid)) local_hits++;

  // Sequence and properties in the interface and module instances
  int hier_hits = 0;
  cover property (@(posedge clk) bus.s_valid(bus.valid)) hier_hits++;
  assert property (@(posedge clk) bus.p_data(bus.valid, bus.data));
  assert property (@(posedge clk) u_sub.p_true);

  always @(posedge clk) begin
    cyc <= cyc + 1;
    bus.valid <= cyc[0];
    bus.data <= cyc[0] ? 8'h5a : 8'h00;
    if (cyc == 10) begin
      `checkd(hier_hits, local_hits);
      if (local_hits == 0) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
