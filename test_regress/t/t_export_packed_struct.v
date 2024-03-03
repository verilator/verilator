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
  udata6_t [3:0] nullptr;  // name confict test
  sub_t          get;      // name confict test
} in_t  /*verilator public*/;

typedef struct packed {
  udata6_t [3:0] nullptr;
  sub_t          get;
  logic [40:0]   a;
} out_t  /*verilator public*/;

// struct in1_t should cover parts of VL_ASSIGNSEL_II functions
typedef struct packed {
  logic [3:0]  a;
  logic [11:0] b;
} in1_t  /*verilator public*/;  // 4 + 12 = 16

typedef struct packed {
  logic [11:0] b;
  logic [3:0]  a;
} out1_t  /*verilator public*/;

// struct in2_t should cover all VL_ASSIGNSEL_II functions
typedef struct packed {
  logic [2:0]  a;
  logic [8:0]  b;
  logic [18:0] c;
} in2_t  /*verilator public*/;  // 3 + 9 + 19 = 31

typedef struct packed {
  logic [8:0]  b;
  logic [18:0] c;
  logic [2:0]  a;
} out2_t  /*verilator public*/;

// struct in3_t should cover all VL_ASSIGNSEL_XQ functions
typedef struct packed {
  logic [1:0]  a;
  logic [8:0]  b;
  logic [16:0] c;
  logic [32:0] d;
} in3_t  /*verilator public*/;  // 33 + 17 + 9 + 2 = 61

typedef struct packed {
  logic [8:0]  b;
  logic [1:0]  a;
  logic [32:0] d;
  logic [16:0] c;
} out3_t  /*verilator public*/;

// struct in4_t should cover all VL_ASSIGNSEL_XW functions
typedef struct packed {
  logic [4:0]  a;
  logic [12:0] b;
  logic [24:0] c;
  logic [48:0] d;
  logic [80:0] e;
} in4_t  /*verilator public*/;  // 5 + 13 + 25 + 49 + 81 = 173

typedef struct packed {
  logic [24:0] c;
  logic [48:0] d;
  logic [80:0] e;
  logic [4:0]  a;
  logic [12:0] b;
} out4_t  /*verilator public*/;

module add (
  input  in_t   op1,
  input  in_t   op2,
  output out_t  out,
  // Add some extra ports to test all VL_ASSIGNSEL_XX functions
  input  in1_t  op1a,
  input  in1_t  op1b,
  output out1_t out1,
  // Add some extra ports to test all VL_ASSIGNSEL_XX functions
  input  in2_t  op2a,
  input  in2_t  op2b,
  output out2_t out2,
  // Add some extra ports to test all VL_ASSIGNSEL_XX functions
  input  in3_t  op3a,
  input  in3_t  op3b,
  output out3_t out3,
  // Add some extra ports to test all VL_ASSIGNSEL_XX functions
  input  in4_t  op4a,
  input  in4_t  op4b,
  output out4_t out4
);
  assign out.a = op1.a + op2.a;
  generate
    for (genvar i = 0; i < 4; ++i) begin
      assign out.nullptr[i] = op1.nullptr[i] + op2.nullptr[i];
    end
  endgenerate
  assign out.get.a = op1.get.a + op2.get.a;

  // out1
  assign out1.a    = op1a.a + op1b.a;
  assign out1.b    = op1a.b + op1b.b;

  // out2
  assign out2.a    = op2a.a + op2b.a;
  assign out2.b    = op2a.b + op2b.b;
  assign out2.c    = op2a.c + op2b.c;

  // out3
  assign out3.a    = op3a.a + op3b.a;
  assign out3.b    = op3a.b + op3b.b;
  assign out3.c    = op3a.c + op3b.c;
  assign out3.d    = op3a.d + op3b.d;

  // out4
  assign out4.a    = op4a.a + op4b.a;
  assign out4.b    = op4a.b + op4b.b;
  assign out4.c    = op4a.c + op4b.c;
  assign out4.d    = op4a.d + op4b.d;
  assign out4.e    = op4a.e + op4b.e;

endmodule
