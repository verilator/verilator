// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Leela Pakanati
// SPDX-License-Identifier: CC0-1.0

// Test for Issue #5941 and #2656: Modport interface field access via hierarchy
// Tests:
// - Single-level and deep hierarchical access
// - Multiple interface instances (same modport type, different data)
// - Interface arrays

interface bus_if (
    input logic clk
);
  logic [7:0] data;
  modport slave(output data, input clk);
endinterface

// l1 module with the actual logic
module l1_mod (
    bus_if.slave bus
);
  always_ff @(posedge bus.clk) bus.data <= 8'h5A;
endmodule

// l0 module wrapping l1 module
module l0_mod (
    bus_if.slave bus
);
  l1_mod l1_inst (bus);
endmodule

// Modules for testing multiple instances with same modport
module mod_aa (
    bus_if.slave bus
);
  assign bus.data = 8'hAA;
endmodule

module mod_bb (
    bus_if.slave bus
);
  assign bus.data = 8'hBB;
endmodule

// Module for testing interface arrays
module array_mod (
    bus_if.slave bus[2]
);
  always_ff @(posedge bus[0].clk) begin
    bus[0].data <= 8'hA0;
    bus[1].data <= 8'hA1;
  end
endmodule

module t (
    input clk
);

  integer cyc = 0;

  // Deep hierarchy test
  bus_if bus (clk);
  l0_mod l0_inst (bus);

  // Multiple instances test
  bus_if bus_a (clk);
  bus_if bus_b (clk);
  mod_aa inst_aa (bus_a);
  mod_bb inst_bb (bus_b);

  // Array test
  bus_if bus_arr[2] (clk);
  array_mod array_inst (bus_arr);

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 5) begin
      // === Deep hierarchy tests ===
      $display("bus.data = %h (direct)", bus.data);
      $display("l0_inst.bus.data = %h (single-level)", l0_inst.bus.data);
      $display("l0_inst.l1_inst.bus.data = %h (deep)", l0_inst.l1_inst.bus.data);

      if (bus.data !== 8'h5A) begin
        $display("%%Error: bus.data = %h, expected 5A", bus.data);
        $stop;
      end
      if (l0_inst.bus.data !== 8'h5A) begin
        $display("%%Error: l0_inst.bus.data = %h, expected 5A", l0_inst.bus.data);
        $stop;
      end
      if (l0_inst.l1_inst.bus.data !== 8'h5A) begin
        $display("%%Error: l0_inst.l1_inst.bus.data = %h, expected 5A", l0_inst.l1_inst.bus.data);
        $stop;
      end
      if (l0_inst.bus.clk !== clk) begin
        $display("%%Error: l0_inst.bus.clk mismatch");
        $stop;
      end
      if (l0_inst.l1_inst.bus.clk !== clk) begin
        $display("%%Error: l0_inst.l1_inst.bus.clk mismatch");
        $stop;
      end

      // === Multiple instances tests (bug #2656) ===
      $display("inst_aa.bus.data = %h", inst_aa.bus.data);
      $display("inst_bb.bus.data = %h", inst_bb.bus.data);

      if (inst_aa.bus.data !== 8'hAA) begin
        $display("%%Error: inst_aa.bus.data = %h, expected AA", inst_aa.bus.data);
        $stop;
      end
      if (inst_bb.bus.data !== 8'hBB) begin
        $display("%%Error: inst_bb.bus.data = %h, expected BB", inst_bb.bus.data);
        $stop;
      end

      // === Interface array tests (bug #2656) ===
      $display("bus_arr[0].data = %h (direct)", bus_arr[0].data);
      $display("bus_arr[1].data = %h (direct)", bus_arr[1].data);
      $display("array_inst.bus[0].data = %h (hierarchical)", array_inst.bus[0].data);
      $display("array_inst.bus[1].data = %h (hierarchical)", array_inst.bus[1].data);

      if (bus_arr[0].data !== 8'hA0) begin
        $display("%%Error: bus_arr[0].data = %h, expected A0", bus_arr[0].data);
        $stop;
      end
      if (bus_arr[1].data !== 8'hA1) begin
        $display("%%Error: bus_arr[1].data = %h, expected A1", bus_arr[1].data);
        $stop;
      end
      if (array_inst.bus[0].data !== 8'hA0) begin
        $display("%%Error: array_inst.bus[0].data = %h, expected A0", array_inst.bus[0].data);
        $stop;
      end
      if (array_inst.bus[1].data !== 8'hA1) begin
        $display("%%Error: array_inst.bus[1].data = %h, expected A1", array_inst.bus[1].data);
        $stop;
      end

      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
