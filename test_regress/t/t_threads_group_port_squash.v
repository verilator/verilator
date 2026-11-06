// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Michael Bedford Taylor
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module tile (
    input clk,
    input [7:0] id,
    input [95:0] in,
    output logic [95:0] out
);
  /*verilator threads_group*/
  initial out = 0;
  always @(posedge clk) out <= {out[63:0], out[95:64] + in[31:0] + {24'b0, id}};
endmodule

module t;
  logic clk = 1'b0;
  always #5 clk = ~clk;

  localparam int N = 4;
  int cyc = 0;
  wire [95:0] out[N];
  logic [95:0] ref_out[N];
  for (genvar i = 0; i < N; ++i) begin : g
    tile u (
        .clk(clk),
        .id(8'(i + 1)),
        .in(out[(i+N-1)%N]),
        .out(out[i])
    );
    initial ref_out[i] = 0;
    always @(posedge clk) begin
      `checkh(out[i], ref_out[i])
      ref_out[i] <= {ref_out[i][63:0], ref_out[i][95:64] + ref_out[(i+N-1)%N][31:0] + (i + 1)};
    end
  end
  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 40) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
