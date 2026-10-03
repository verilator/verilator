// DESCRIPTION: Verilator: Subgraph boundary scheduling preserves old values
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while (0)
// verilog_format: on

module t (
  input logic clk
);

  int cyc = 0;
  logic [6:0] a;
  logic [6:0] b;
  logic [6:0] p = 7'd1;
  logic [6:0] parent_sample = 7'd0;
  logic reset = 1'b1;

  sg_rotate i_a (
    .clk(clk),
    .reset(reset),
    .reset_value(7'd2),
    .data_in(b),
    .data_out(a)
  );
  sg_rotate i_b (
    .clk(clk),
    .reset(reset),
    .reset_value(7'd3),
    .data_in(p),
    .data_out(b)
  );

  always_ff @(posedge clk) begin
    cyc <= cyc + 1;
    reset <= 1'b0;
    if (reset) begin
      p <= 7'd1;
      parent_sample <= 7'd0;
    end
    else begin
      p <= a;
      parent_sample <= a + b;
    end

    if (cyc >= 1) begin
      case ((cyc - 1) % 3)
        0: begin
          `checkh(p, 7'd1);
          `checkh(a, 7'd2);
          `checkh(b, 7'd3);
        end
        1: begin
          `checkh(p, 7'd2);
          `checkh(a, 7'd3);
          `checkh(b, 7'd1);
          `checkh(parent_sample, 7'd5);
        end
        2: begin
          `checkh(p, 7'd3);
          `checkh(a, 7'd1);
          `checkh(b, 7'd2);
          `checkh(parent_sample, 7'd4);
        end
      endcase
    end

    if (cyc == 10) begin
      `checkh(parent_sample, 7'd3);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule

module sg_rotate (
  input logic clk,
  input logic reset,
  input logic [6:0] reset_value,
  input logic [6:0] data_in,
  output logic [6:0] data_out
);
`ifndef USE_VLT
  /*verilator subgraph_boundary*/
`endif

  logic [6:0] state = 7'd0;

  always_ff @(posedge clk) begin
    if (reset) state <= reset_value;
    else state <= data_in;
  end

  assign data_out = state;

endmodule
