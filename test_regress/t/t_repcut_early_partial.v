// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input logic clk,
    input logic [1:0] addr,
    input logic [7:0] data,
    output logic [7:0] value
);
`ifdef REPCUT_MEMORY
  logic [7:0] mem [0:3];
  always @(posedge clk) begin
    mem[addr] <= data;
    if (data[0]) begin
      if (data[1]) mem[2] <= mem[addr] ^ data;
      else mem[1] <= data;
    end
    value <= mem[addr];
  end
`elsif REPCUT_CONSTANT_INIT
  initial value = 8'h5a;
`elsif REPCUT_INPUT_INIT
  initial value = data;
`elsif REPCUT_COND_INIT
  initial if (addr[0]) value = 8'h5a;
`elsif REPCUT_INIT_WRITERS
  initial value = 8'h5a;
  initial value = 8'ha5;
`elsif REPCUT_MEMORY_ODD
  logic [7:0] mem [0:2];
  always @(posedge clk) begin
    mem[addr] <= data;
    value <= mem[addr];
  end
`elsif REPCUT_MEM_WRITERS
  logic [7:0] mem [0:3];
  always @(posedge clk) mem[addr] <= data;
  always @(posedge clk) mem[2] <= ~data;
  assign value = mem[addr];
`elsif REPCUT_MEM_BOUNDS
  logic [7:0] mem [5:8];
  always @(posedge clk) mem[5] <= data;
  assign value = mem[5];
`elsif REPCUT_ROM_BLOCKING
  logic [7:0] mem [0:3] = '{default: 8'h5a};
  always @(posedge clk) mem[addr] = data;
  assign value = mem[addr];
`elsif REPCUT_ROM_UNINITIALIZED
  logic [7:0] mem [0:3];
  assign value = mem[addr];
`elsif REPCUT_GATED_CLOCK
  wire capture_clock = clk & addr[0];
  always @(posedge capture_clock) value <= data;
`elsif REPCUT_INVERTED_CLOCK
  wire capture_clock = ~clk;
  always @(posedge capture_clock) value <= data;
`elsif REPCUT_CLOCK_CYCLE
  wire capture_clock;
  wire other_clock;
  assign capture_clock = other_clock;
  assign other_clock = capture_clock;
  always @(posedge capture_clock) value <= data;
`elsif REPCUT_CLOCK_WRITERS
  logic capture_clock;
  assign capture_clock = clk;
  always_latch if (addr[0]) capture_clock = addr[1];
  always @(posedge capture_clock) value <= data;
`elsif REPCUT_CYCLE
  assign value = (value << 1) ^ data;
`elsif REPCUT_DOMAIN
  logic [7:0] rising;
  logic [7:0] falling;
  always @(posedge clk) rising <= data;
  always @(negedge clk) falling <= data;
  assign value = rising ^ falling;
`elsif REPCUT_EFFECT
  always @(posedge clk) begin
    value <= data;
    $display("This side effect must not be replicated");
  end
`else
  logic [7:0] mem [0:3][0:3];
  always @(posedge clk) mem[addr][addr] <= data;
  assign value = mem[addr][addr];
`endif
endmodule
