// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;

  wire [5:0] b1 = 6'b101101;
  wire [5:0] b2 = 6'b011110;
  logic [5:0] a6;
  logic [9:0] a10;
  logic [5:0] lhs;
  logic [5:0] rhs;
  logic [4:0] narrow;
  typedef int word_t;
  int sum;
  bit equals_64;

  function automatic int cast_argument(input int value);
    return value;
  endfunction

  initial begin
    // issue #3417
    a6 = b2 - b1;
    `checkh(a6, 6'h31);
    a10 = 10'(b2 - b1);
    `checkh(a10, 10'h3f1);  // This being not 31 indicates operator expands
    `checkh($bits(10'(b1)), 10);
    `checkh($bits(10'(b2 - b1)), 10);
    `checkh($bits(b2 - b1), 6);
    // issue #3923: A type cast widens the operation without a width warning.
    lhs = 6'd45;
    rhs = 6'd30;
    sum = int'(lhs + rhs);
    `checkh(sum, 32'd75);  // The cast widens the addition before it can overflow.
    narrow = 5'd25;
    sum = word_t'(lhs + narrow);
    `checkh(sum, 32'd70);
    // Explicit casts inside arguments and lambdas still suppress local warnings.
    sum = int'(cast_argument(int'(lhs + narrow)));
    `checkh(sum, 32'd70);
    begin
      logic [5:0] values[$];
      values = '{lhs, rhs};
      sum = int'(values.sum() with (int'(item + narrow)));
      `checkh(sum, 32'd125);
    end
    sum = int'(real'(int'(lhs == narrow)));
    `checkh(sum, 32'd0);
    sum = int'((lhs + rhs) + (lhs - narrow));
    `checkh(sum, 32'd95);
    sum = 32'((lhs + rhs) + (lhs - narrow));
    `checkh(sum, 32'd95);
    sum = int'(lhs == narrow);
    `checkh(sum, 32'd0);
    lhs = 6'd40;
    rhs = 6'd24;
    equals_64 = int'(lhs + rhs) == 64;
    `checkh(equals_64, 1'b1);
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
