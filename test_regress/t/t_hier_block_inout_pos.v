// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: got=%p exp=%p (%s !== %s)\n", `__FILE__, `__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while (0);
// verilog_format: on

module t;
  logic clk = 1'b0;
  always #5 clk = ~clk;
  logic [6:0] cnt = 7'h35;
  wire [6:0] din_w = cnt;
  wire [6:0] en_w = 7'h00;
  wire [6:0] bus;
  wire [6:0] seen;
  wire [6:0] seen_var;
  wire [6:0] bus_var;
  logic [6:0] en_var = 0;
  int cyc = 0;
  // Split inout ports must follow these original positional connections.
  sub u_sub (
      din_w,
      en_w,
      bus,
      seen
  );
  sub u_var (
      cnt,
      en_var,
      bus_var,
      seen_var
  );
  always @(posedge clk) begin
    cyc <= cyc + 1;
    cnt <= cnt + 7'd3;
    if (cyc > 2) begin
      `checkh(seen, cnt ^ 7'h11);
      `checkh(seen_var, cnt ^ 7'h11);
    end
    if (cyc == 10) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
module sub (
    input logic [6:0] din,
    input logic [6:0] en,
    inout wire [6:0] bus,
    output logic [6:0] seen
);  /*verilator hier_block*/
  assign bus = en[0] ? din : 7'bz;
  assign seen = din ^ 7'h11;
endmodule
