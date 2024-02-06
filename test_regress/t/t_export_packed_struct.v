// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Kefa Chen.
// SPDX-License-Identifier: CC0-1.0

typedef logic [5:0] udata6_t;

typedef union packed {
  udata6_t    a;
  logic [2:0] b;
} sub_t;

typedef struct packed {
  logic [40:0]   a;
  udata6_t [3:0] b;
  sub_t          c;
} in_t  /*verilator public*/;

typedef struct packed {
  udata6_t [3:0] b;
  sub_t          c;
  logic [40:0]   a;
} out_t  /*verilator public*/;

module add (
  input  in_t  op1,
  input  in_t  op2,
  output out_t out
);
  assign out.a = op1.a + op2.a;
  generate
    for (genvar i = 0; i < 4; ++i) begin
      assign out.b[i] = op1.b[i] + op2.b[i];
    end
  endgenerate
  assign out.c.a = op1.c.a + op2.c.a;

endmodule
