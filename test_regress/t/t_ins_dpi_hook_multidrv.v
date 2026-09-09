// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Output targets with several drivers (case branches of one block, outputs of one module
// driven by an assignment and by a submodule port)
module top_module;
  logic       clk = 0;
  logic [7:0] a = 8'h11;
  logic [1:0] sel = 0;
  logic [7:0] q, q2;
  logic [7:0] qa, qb;

  sub s (.a(a), .sel(sel), .o(q), .o2(q2));
  mid m (.a(a), .oa(qa), .ob(qb));

  int cyc = 0;
  always #5 clk = ~clk;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    sel <= sel + 1;
    a   <= a + 1;
    if (cyc > 20) begin
      $display("*-* All Finished *-*");
      $finish;
    end
  end
endmodule

module sub (
  input  logic [7:0] a,
  input  logic [1:0] sel,
  output logic [7:0] o,
  output logic [7:0] o2
);

  always_comb begin
    case (sel)
      2'd0:    o = a;
      2'd1:    o = a << 1;
      2'd2:    o = a + 8'd3;
      default: o = ~a;
    endcase
  end

  assign o2 = o ^ 8'hAA;
endmodule

module mid (
  input  logic [7:0] a,
  output logic [7:0] oa,
  output logic [7:0] ob
);
  assign oa = a + 8'd1;
  leaf l (.x(a), .y(ob));
endmodule

module leaf (
  input  logic [7:0] x,
  output logic [7:0] y
);
  assign y = x ^ 8'h55;
endmodule
