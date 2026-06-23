// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

package pkg;
  typedef struct {
    logic [7:0] value;
  } field_t;
  typedef struct {
    field_t f0;
    field_t f1;
  } reg_t;
  typedef struct {
    reg_t R0;
    reg_t R1;
    reg_t R2;
  } hwif_t;
endpackage

module t (/*AUTOARG*/
  // Inputs
  clk
  );
  input clk;

  import pkg::*;

  hwif_t hwif_in;
  hwif_t hwif_out;
  hwif_t storage;

  integer cyc = 0;

  always_ff @(posedge clk) begin
    storage.R0.f0.value <= hwif_in.R0.f0.value;
    storage.R0.f1.value <= hwif_in.R0.f1.value;
    storage.R1.f0.value <= hwif_in.R1.f0.value;
    storage.R1.f1.value <= hwif_in.R1.f1.value;
    storage.R2.f0.value <= hwif_in.R2.f0.value;
    storage.R2.f1.value <= hwif_in.R2.f1.value;
  end

  always_comb begin
    hwif_out.R0.f0.value = storage.R0.f0.value;
    hwif_out.R0.f1.value = storage.R0.f1.value;
    hwif_out.R1.f0.value = storage.R1.f0.value;
    hwif_out.R1.f1.value = storage.R1.f1.value;
    hwif_out.R2.f0.value = storage.R2.f0.value;
    hwif_out.R2.f1.value = storage.R2.f1.value;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 0) begin
      hwif_in.R0.f0.value <= 8'h11;
      hwif_in.R0.f1.value <= 8'h22;
      hwif_in.R1.f0.value <= 8'h33;
      hwif_in.R1.f1.value <= 8'h44;
      hwif_in.R2.f0.value <= 8'h55;
      hwif_in.R2.f1.value <= 8'h66;
    end
    else if (cyc == 3) begin
      if (hwif_out.R0.f0.value !== 8'h11) $stop;
      if (hwif_out.R0.f1.value !== 8'h22) $stop;
      if (hwif_out.R1.f0.value !== 8'h33) $stop;
      if (hwif_out.R1.f1.value !== 8'h44) $stop;
      if (hwif_out.R2.f0.value !== 8'h55) $stop;
      if (hwif_out.R2.f1.value !== 8'h66) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
