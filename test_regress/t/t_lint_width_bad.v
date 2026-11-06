// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2009 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

  // See also t_math_width

  // This shows the uglyness in width warnings across param modules
  // TODO: Would be nice to also show relevant parameter settings
  p #(.WIDTH(4)) p4 (.in(4'd0));
  p #(.WIDTH(5)) p5 (.in(5'd0));

  //====
  localparam [3:0] XS = 'hx;  // User presumably intended to use 'x

  //====
  wire [4:0] c = 1'b1 << 2;  // No width warning, as is common syntax
  wire [4:0] d = (1'b1 << 2) + 5'b1;  // Has warning as not obvious what expression width is

  //====
  localparam WIDTH = 6;
  wire one_bit;
  wire [2:0] shifter = 1;
  wire [WIDTH-1:0] masked = (({{(WIDTH) {1'b0}}, one_bit}) << shifter);

  //====
  // We presently warn here, in theory we could detect if the number of one bit additions could overflow the LHS
  wire one = 1;
  wire [2:0] cnt = (one + one + one + one);

  // Not harmless > or >= compared with something wider (as different results if "a" wider)
  localparam [40:0] THREE = 3;
  int a;
  initial for (a = 0; a > THREE; ++a) $display(a);
  initial for (a = 0; a >= THREE; ++a) $display(a);

  initial if (THREE) $stop;

  // A cast of a call or reference must not suppress warnings in its definition.
  initial begin
    $display("%0d", int'(cast_add(6'd45, 5'd25)));
    $display("%0d", int'(cast_value));
    $display("%0d", int'(CAST_ENUM_VALUE));
  end
  function automatic int cast_add(input logic [5:0] lhs, input logic [4:0] rhs);
    return lhs + rhs;
  endfunction
  int cast_value = 6'd45 + 5'd25;
  typedef enum int { CAST_ENUM_VALUE = 6'd45 + 5'd25 } cast_enum_t;

  // A non-integral cast does not suppress operand width warnings.
  initial $display("%f", real'(6'd45 == 5'd25));

  // A nested cast's type expression is checked independently of its operand.
  initial $display("%0d", int'(type(6'd45 == 5'd25)'(1'b1)));

endmodule

module p #(
    parameter WIDTH = 64
) (
    input [WIDTH-1:0] in
);
  wire [4:0] out = in;
endmodule
