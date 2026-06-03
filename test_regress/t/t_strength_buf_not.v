// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkb(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='b%x exp='b%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Based on iverilog/ivtest/ivltests/br918c.v by Cary R

module driver (
    inout wire b0,
    inout wire b1,
    inout wire b2,
    inout wire b3
);

  reg [3:0] v;

  buf (strong0, pull1) u_buf0 (b0, v[0]);
  buf (strong0, pull1) u_buf1 (b1, v[1]);

  not (strong0, pull1) u_not2 (b2, v[2]);
  not (strong0, pull1) u_not3 (b3, v[3]);

  initial v = 4'b1010;

endmodule

module t (input clk);

  wire [3:0] bus;

  pullup u_pu0 (bus[0]);
  pullup u_pu1 (bus[1]);
  pullup u_pu2 (bus[2]);
  pullup u_pu3 (bus[3]);

  driver u_driver (
      .b0(bus[0]),
      .b1(bus[1]),
      .b2(bus[2]),
      .b3(bus[3])
  );

  initial begin
    #1;
    `checkb(bus, 4'b0110);
    $finish;
  end

endmodule
