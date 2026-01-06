// DESCRIPTION: Verilator: Get agregate type parameter from array of interfaces
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2024 by Todd Strader
// SPDX-License-Identifier: CC0-1.0

typedef struct {
  int BAR_INT;
  bit BAR_BIT;
  byte BAR_ARRAY[0:3];
} foo_t;

interface intf #(
    parameter foo_t FOO = '{4, 1'b1, '{8'd1, 8'd2, 8'd4, 8'd8}}
) (
    input wire clk,
    input wire rst
);
  modport modp(input clk, rst);
endinterface

module sub (
    intf.modp the_intf_port[4],
    intf.modp single_intf_port
);
  localparam foo_t intf_foo = the_intf_port[0].FOO;
  localparam int intf_foo_bar_int = the_intf_port[0].FOO.BAR_INT;
  localparam bit intf_foo_bar_bit = the_intf_port[0].FOO.BAR_BIT;
  localparam byte intf_foo_bar_byte = the_intf_port[0].FOO.BAR_ARRAY[3];
  localparam foo_t single_foo = single_intf_port.FOO;
  localparam int single_foo_bar_int = single_intf_port.FOO.BAR_INT;
  localparam bit single_foo_bar_bit = single_intf_port.FOO.BAR_BIT;
  localparam byte single_foo_bar_byte = single_intf_port.FOO.BAR_ARRAY[3];

  initial begin
    if (intf_foo != foo_t'{4, 1'b1, '{1, 2, 4, 8}}) $stop;
    if (intf_foo_bar_int != 4) $stop;
    if (intf_foo_bar_bit != 1'b1) $stop;
    if (intf_foo_bar_byte != 8'd8) $stop;
    if (single_foo != foo_t'{4, 1'b1, '{1, 2, 4, 8}}) $stop;
    if (single_foo_bar_int != 4) $stop;
    if (single_foo_bar_bit != 1'b1) $stop;
    if (single_foo_bar_byte != 8'd8) $stop;
  end
endmodule

module t (
    clk
);
  logic rst;
  input clk;

  intf the_intf[4] (.*);
  intf single_intf (.*);

  sub the_sub (
      .the_intf_port(the_intf),
      .single_intf_port(single_intf)
  );

  always @(posedge clk) begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
