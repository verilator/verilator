// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2021 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t_assert;
  logic clk;
  logic zeroize;
  logic [7:0] key_mem [0:0];
  assert property (@(posedge clk) zeroize |=> (key_mem[0] == 0));
  initial force zeroize = 0;
endmodule

module t (
    input clk
);

  t_assert t_assert_i();

  integer cyc = 0;
  localparam logic [95:0] WIDE_INIT = 96'h12345678_9abcdef0_13579bdf;
  localparam logic [94:0] WIDE_FORCE95 = {3'b101, 32'h12345678, 32'h89abcdef, 28'h2468ace};

  reg [3:0] in;
  tri [3:0] bus = in;
  logic [95:0] wide_src;
  wire [95:0] wide_bus = wide_src;
  logic [7:0] unpacked [0:3];

  int never_driven;
  int never_forced;

  real r;

  task force_bus;
    force bus[1:0] = 2'b10;
  endtask

  task release_bus;
    release bus;
  endtask

  // Test loop
  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 0) begin
      in <= 4'b0101;
    end
    else if (cyc == 1) begin
      `checkh(in, 4'b0101);
    end
    // Check forces with no driver
    if (cyc == 1) begin
      force never_driven = 32'h888;
    end
    else if (cyc == 2) begin
      `checkh(never_driven, 32'h888);
    end
    //
    // Check release with no force
    else if (cyc == 10) begin
      never_forced <= 5432;
    end
    else if (cyc == 11) begin
      `checkh(never_forced, 5432);
    end
    else if (cyc == 12) begin
      release never_forced;  // no-op
    end
    else if (cyc == 13) begin
      `checkh(never_forced, 5432);
    end
    //
    // bus
    else if (cyc == 20) begin
      `checkh(bus, 4'b0101);
      force bus = 4'b0111;
    end
    else if (cyc == 21) begin
      `checkh(bus, 4'b0111);
      force bus = 4'b1111;
    end
    else if (cyc == 22) begin
      `checkh(bus, 4'b1111);
      release bus;
    end
    else if (cyc == 23) begin
      `checkh(bus, 4'b0101);
    end
    //
    else if (cyc == 30) begin
      force_bus();
    end
    else if (cyc == 31) begin
      `checkh(bus, 4'b0110);
    end
    else if (cyc == 32) begin
      release bus[0];
    end
    else if (cyc == 33) begin
      `checkh(bus, 4'b0111);
      release_bus();
    end
    else if (cyc == 34) begin
      `checkh(in, 4'b0101);
      `checkh(bus, 4'b0101);
    end
    //
    else if (cyc == 35) begin
      force bus = 4'b1111;
    end
    else if (cyc == 36) begin
      `checkh(bus, 4'b1111);
      force bus[3:1] = 3'b000;
    end
    else if (cyc == 37) begin
      `checkh(bus, 4'b0001);
      release bus[2];
    end
    else if (cyc == 38) begin
      `checkh(bus, 4'b0101);
      release bus;
    end
    else if (cyc == 39) begin
      `checkh(bus, 4'b0101);
    end
    //
    else if (cyc == 40) begin
      r <= 1.25;
    end
    else if (cyc == 41) begin
      `checkr(r, 1.25);
    end
    else if (cyc == 42) begin
      force r = 2.5;
    end
    else if (cyc == 43) begin
      `checkr(r, 2.5);
    end
    else if (cyc == 44) begin
      release r;
    end
    else if (cyc == 45) begin
      `checkr(r, 2.5);
    end
    //
    else if (cyc == 50) begin
      wide_src <= WIDE_INIT;
    end
    else if (cyc == 51) begin
      `checkh(wide_bus, WIDE_INIT);
    end
    else if (cyc == 52) begin
      force wide_bus[95:1] = WIDE_FORCE95;
    end
    else if (cyc == 53) begin
      `checkh(wide_bus, {WIDE_FORCE95, WIDE_INIT[0]});
    end
    else if (cyc == 54) begin
      release wide_bus[95:1];
    end
    else if (cyc == 55) begin
      `checkh(wide_bus, WIDE_INIT);
    end
    //
    else if (cyc == 60) begin
      unpacked[0] <= 8'h10;
      unpacked[1] <= 8'h20;
      unpacked[2] <= 8'h30;
      unpacked[3] <= 8'h40;
    end
    else if (cyc == 61) begin
      `checkh(unpacked[0], 8'h10);
      `checkh(unpacked[1], 8'h20);
      `checkh(unpacked[2], 8'h30);
      `checkh(unpacked[3], 8'h40);
    end
    else if (cyc == 62) begin
      force unpacked[1] = 8'hb1;
      force unpacked[2] = 8'hc2;
    end
    else if (cyc == 63) begin
      `checkh(unpacked[0], 8'h10);
      `checkh(unpacked[1], 8'hb1);
      `checkh(unpacked[2], 8'hc2);
      `checkh(unpacked[3], 8'h40);
    end
    else if (cyc == 64) begin
      release unpacked[1];
      release unpacked[2];
    end
    else if (cyc == 65) begin
      `checkh(unpacked[0], 8'h10);
      `checkh(unpacked[1], 8'hb1);
      `checkh(unpacked[2], 8'hc2);
      `checkh(unpacked[3], 8'h40);
      unpacked[1] <= 8'h21;
      unpacked[2] <= 8'h32;
    end
    else if (cyc == 66) begin
      `checkh(unpacked[0], 8'h10);
      `checkh(unpacked[1], 8'h21);
      `checkh(unpacked[2], 8'h32);
      `checkh(unpacked[3], 8'h40);
    end
    //
    else if (cyc == 99) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
