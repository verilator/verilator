// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2010 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  integer i;

  reg sync_blk;
  reg sync_blk2;
  reg sync_nblk;
  reg sync2_ok;
  reg sync3_ok;
  reg combo_blk;
  reg combo_nblk;

  always @(posedge clk) begin
    sync_blk = 1'b1;
    sync_blk2 = 1'b1;  // Only warn once per block
    sync_nblk <= 1'b1;
  end

  always_comb begin
    combo_blk = 1'b1;
    combo_nblk <= 1'b1;
  end

  always @(posedge clk) begin
    for (int i = 0; i < 20; i++) begin
      sync2_ok <= 1'b1;
    end
  end

  always @(posedge clk) begin
    sync3_ok <= f(sync3_ok);
  end

  function f(input v);
    f = ~v;
  endfunction

  logic single;
  logic array[1:0];

  DoesBlockingAssignA a (
      .clk(clk),
      .out(single)
  );

  DoesBlockingAssignB b (
      .clk(clk),
      .out(array[0])
  );

endmodule

module DoesBlockingAssignA (
    input wire clk,
    output reg out
);

  always @(posedge clk) out = 1;

endmodule

module DoesBlockingAssignB (
    input wire clk,
    output reg out
);

  always @(posedge clk) out = 1;

endmodule
