// DESCRIPTION: Verilator: Test covergroup clocked (automatic) sampling
// Tests --no-timing (default) mode; see t_covergroup_auto_sample_timing for --timing variant.
// This file ONLY is placed into the Public Domain, for any use, without warranty.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
  // Inputs
  clk
  );
  input clk;

  logic [1:0] data;

  // Covergroup with automatic sampling on posedge clk
  covergroup cg @(posedge clk);
    cp_data: coverpoint data {
      bins zero  = {2'b00};
      bins one   = {2'b01};
      bins two   = {2'b10};
      bins three = {2'b11};
    }
  endgroup

  cg cg_inst = new;

  int cyc = 0;

  always @(posedge clk) begin
    cyc <= cyc + 1;

    case (cyc)
      0: data <= 2'b00;
      1: data <= 2'b01;
      2: data <= 2'b10;
      3: data <= 2'b11;
      4: begin
        $write("*-* All Finished *-*\n");
        $finish;
      end
    endcase

    // NOTE: NO manual .sample() call - relying on automatic sampling!
  end
endmodule
