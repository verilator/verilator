// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

  bit valid;
  bit clk;
  logic [7:0] out;
  logic [7:0] in;

  initial begin
    valid = 1;
    out = 2;
    in = 2;
  end

  property prop;
    @(posedge clk) (valid) |-> ##2 (out == in + 3);
  endproperty

  assert property (prop);

  initial begin
    forever begin
      #(10) clk = ~clk;
    end
  end

  initial #200 $finish;

endmodule
