// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Kefa Chen.
// SPDX-License-Identifier: CC0-1.0

// Packed struct in package
package TEST_TYPES;
  typedef union packed {
    logic [64:0] a;
    logic [2:0]  b;
  } sub_t;
  typedef struct packed {
    struct packed {  // Anonymous packed struct
      logic a;
    } anon;
    TEST_TYPES::sub_t [2:0][2:0][2:0] b;
  } in_t  /*verilator public*/;
  typedef struct packed {
    TEST_TYPES::sub_t [2:0][2:0][2:0] b;
    struct packed {logic a;} anon;
  } out_t  /*verilator public*/;
endpackage

// Packed struct in class
class cls_in;
  typedef struct packed {
    logic a;
    TEST_TYPES::sub_t [2:0][2:0][2:0] b;
  } in_t  /*verilator public*/;
  in_t in;
endclass  //cls

module add (
  input  TEST_TYPES::in_t  op1,
  //input  cls_in  op2,
  output TEST_TYPES::out_t out
);
  cls_in op2 /*verilator public_flat*/;

  initial begin
    if(op2 != null) $stop;
    op2 = new();
    if(!op2) $stop;
  end

  assign op2.in.a = op1.anon.a;
  generate
    for (genvar i = 0; i < 3; ++i) begin
      for (genvar j = 0; j < 3; ++j) begin
        for (genvar k = 0; k < 3; ++k) begin
          assign op2.in.b[i][j][k] = op1.b[i][j][k];
        end
      end
    end
  endgenerate

  assign out.anon.a = op1.anon.a + op2.in.a;
  generate
    for (genvar i = 0; i < 3; ++i) begin
      for (genvar j = 0; j < 3; ++j) begin
        for (genvar k = 0; k < 3; ++k) begin
          assign out.b[i][j][k] = op1.b[i][j][k] + op2.in.b[i][j][k];
        end
      end
    end
  endgenerate

endmodule
