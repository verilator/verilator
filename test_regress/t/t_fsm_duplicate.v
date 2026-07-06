// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module rr #(
) (
    input logic clk,
    input logic rst,
    input logic [7:0] data,
    input logic data_q
);
  logic a;
  logic [15:0] dcnt;
  typedef enum logic [7:0] {
    S0,
    S1,
    S2,
    S3
  } state_t;
  state_t state_d, state_q;
  always_ff @(posedge clk or negedge rst) if (!rst) state_q <= S0;
  always_ff @(posedge clk)
    unique case (state_q)
      S1: if (a) dcnt[7:0] <= data;
      S2: if (a) dcnt[15:8] <= data;
      S3: if (data_q) dcnt <= dcnt - 1;
      default: dcnt <= dcnt;
    endcase
endmodule
module re #(
) (
    input logic clk,
    input logic rst,
    output logic o,
    input unused0,  /* block optimizations */
    input unused1,
    input unused2,
    input unused3,
    input unused4,
    input unused5,
    input unused6,
    input unused7,
    input unused8,
    input unused9,
    input unused10,
    input unused11,
    input unused12,
    input unused13,
    input unused14,
    input unused15,
    input unused16,
    input unused17,
    input unused18,
    input unused19,
    input unused20,
    input unused21,
    input unused22,
    input unused23,
    input unused24,
    input unused25,
    input unused26,
    input unused27,
    input unused28,
    input unused29,
    input unused30,
    input unused31,
    input unused32,
    input unused33,
    input unused34,
    input unused35,
    input unused36,
    input unused37,
    input unused38,
    input unused39,
    input unused40
);
  logic [15:0] dcnt;
  typedef enum logic [7:0] {
    S0,
    S1
  } state_t;
  state_t state_d, state_q;
  always_ff @(posedge clk or negedge rst) if (!rst) state_q <= S0;
  always_ff @(posedge clk)
    unique case (state_q)
      S1: o <= dcnt[0];
      default: o <= '0;
    endcase
  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
module rh #(
) (
    input logic clk
);
  logic [7:0] a;
  logic b;
  logic c;
  logic d;
  logic rst;
  rr xrr (
      .clk,
      .rst(rst),
      .data(a),
      .data_q(b & c)
  );
  re xre (
      .clk,
      .rst(rst),
      .o(d)
  );
endmodule
module U #(
) (
    input clk,
    input rst
);
  rh xrh (.clk(clk));
endmodule
module C #(
) (
    input clk,
    input rst
);
  U U (
      .clk,
      .rst
  );
endmodule
module A #() ();
  logic clk;
  logic rst;
  C c0 (
      .clk,
      .rst
  );
  C c1 (
      .clk,
      .rst
  );
endmodule
module B #() ();
  logic clk;
  logic rst;
  C xC (
      .clk,
      .rst
  );
endmodule
module t #() ();
  B b ();
  A a ();
endmodule
