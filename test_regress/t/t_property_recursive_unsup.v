// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2022 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  int cyc = 0;
  logic val = 0;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    val = ~val;
  end

  property check(int n);
    disable iff (n == 0) check(
        n - 1
    );
  endproperty

  assert property (@(posedge clk) check(1))
  else begin
    // Assertion should pass
    $write("*-* Assertion failed *-*\n");
    $stop;
  end


  // Nested recursive instances (#8295)
  property p_self;
    val |-> p_self;
  endproperty

  property p_mutual1;
    val |-> p_mutual2;
  endproperty

  property p_mutual2;
    !val |-> p_mutual1;
  endproperty

  assert property (@(posedge clk) val |-> p_self);
  assert property (@(posedge clk) val |-> p_mutual1);

  always @(posedge clk) begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
