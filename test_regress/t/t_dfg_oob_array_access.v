// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0


module t (
    input clk
);
  wire mem_wire;
  bit [15:0] idx = 65535;
  bit mem_reg[0:34000];
  assign mem_wire = mem_reg[idx];

  always @(posedge clk) begin
    if (idx < 65533) begin
      $display("oob_val %d", mem_wire);
      $write("*-* All Finished *-*\n");
      $finish;
    end
    else begin
      idx <= idx - 1;
      mem_reg[idx] <= 0;
    end
  end
endmodule
