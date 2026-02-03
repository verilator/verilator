// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Leela Pakanati
// SPDX-License-Identifier: CC0-1.0

// Test for Issue #5941: Modport interface field access via hierarchy

interface bus_if (input logic clk);
  logic [7:0] data;
  modport slave (output data, input clk);
endinterface

module slave_mod (bus_if.slave bus);
  always_ff @(posedge bus.clk)
    bus.data <= 8'h5A;
endmodule

module t (/*AUTOARG*/
  // Inputs
  clk
  );

  input clk;
  integer cyc=0;

  bus_if bus (clk);
  slave_mod slave_inst (bus);

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc==5) begin
      // Test hierarchical access through modport interface ports (Issue #5941)
      $display("bus.data = %h (direct)", bus.data);
      $display("slave_inst.bus.data = %h (hierarchical)", slave_inst.bus.data);

      // Verify values
      if (bus.data !== 8'h5A) begin
        $display("%%Error: bus.data = %h, expected 5A", bus.data);
        $stop;
      end
      if (slave_inst.bus.data !== 8'h5A) begin
        $display("%%Error: slave_inst.bus.data = %h, expected 5A", slave_inst.bus.data);
        $stop;
      end

      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
