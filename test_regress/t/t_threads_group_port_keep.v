// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Michael Bedford Taylor
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module sub (
    input clk,
    input [7:0] x,
    output logic [7:0] y
);
  initial y = 0;
  always @(posedge clk) y <= y + x;
endmodule

// The threads_group module; its input ports are kept per instance
module tile (
    input clk,
    input [7:0] id,
    input [15:0] in,
    input [7:0] arr[2],
    output logic [15:0] out
);
  logic [7:0] s;
  // A child input connected straight to a kept port
  sub u_sub (
      .clk(clk),
      .x(id),
      .y(s)
  );
  initial out = 0;
  // The elements of the kept array port are split
  always @(posedge clk) out <= in + {8'b0, s} + {8'b0, id} + {arr[0], arr[1]};
endmodule

module t (
    input clk
);
  localparam int N = 4;
  int cyc = 0;
  wire [15:0] out[N];
  logic [7:0] arrs[N][2];
  logic [15:0] ref_out[N];
  logic [7:0] ref_s[N];
  always_comb
    for (int i = 0; i < N; ++i) begin
      arrs[i][0] = 8'(cyc + i);
      arrs[i][1] = 8'(cyc * i);
    end
  for (genvar i = 0; i < N; ++i) begin : g
    tile u (
        .clk(clk),
        .id(8'(i + 1)),
        .in(out[(i+N-1)%N]),
        .arr(arrs[i]),
        .out(out[i])
    );
    initial begin
      ref_out[i] = 0;
      ref_s[i] = 0;
    end
    always @(posedge clk) begin
      `checkh(out[i], ref_out[i])
      ref_s[i] <= ref_s[i] + 8'(i + 1);
      ref_out[i] <= ref_out[(i+N-1)%N] + {8'b0, ref_s[i]} + 16'(i + 1)
                    + {arrs[i][0], arrs[i][1]};
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

`verilator_config
threads_group -module "tile"
