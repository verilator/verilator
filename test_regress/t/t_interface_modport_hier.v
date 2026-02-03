// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Leela Pakanati
// SPDX-License-Identifier: CC0-1.0

// Test for Issue #5941: Modport interface field access via hierarchy
// Tests single-level and deep hierarchical access using single module chain

interface bus_if (input logic clk);
  logic [7:0] data;
  modport slave (output data, input clk);
endinterface

// Inner module with the actual logic
module inner_mod (bus_if.slave bus);
  always_ff @(posedge bus.clk)
    bus.data <= 8'h5A;
endmodule

// Outer module wrapping inner module
module outer_mod (bus_if.slave bus);
  inner_mod inner_inst (bus);
endmodule

module t (/*AUTOARG*/
  // Inputs
  clk
  );

  input clk;
  integer cyc = 0;

  bus_if bus (clk);
  outer_mod outer_inst (bus);

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 5) begin
      // Test direct access
      $display("bus.data = %h (direct)", bus.data);

      // Test single-level hierarchical access (through outer_mod)
      $display("outer_inst.bus.data = %h (single-level)", outer_inst.bus.data);

      // Test deep hierarchical access (through outer_mod -> inner_mod)
      $display("outer_inst.inner_inst.bus.data = %h (deep)", outer_inst.inner_inst.bus.data);

      // Verify values
      if (bus.data !== 8'h5A) begin
        $display("%%Error: bus.data = %h, expected 5A", bus.data);
        $stop;
      end
      if (outer_inst.bus.data !== 8'h5A) begin
        $display("%%Error: outer_inst.bus.data = %h, expected 5A", outer_inst.bus.data);
        $stop;
      end
      if (outer_inst.inner_inst.bus.data !== 8'h5A) begin
        $display("%%Error: outer_inst.inner_inst.bus.data = %h, expected 5A", outer_inst.inner_inst.bus.data);
        $stop;
      end

      // Test clk access through hierarchy
      if (outer_inst.bus.clk !== clk) begin
        $display("%%Error: outer_inst.bus.clk mismatch");
        $stop;
      end
      if (outer_inst.inner_inst.bus.clk !== clk) begin
        $display("%%Error: outer_inst.inner_inst.bus.clk mismatch");
        $stop;
      end

      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
