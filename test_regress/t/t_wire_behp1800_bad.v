// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2018 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    output o,
    output [1:0] oa,
    output reg ro,
    [1:0] rn,
    output reg [1:0] roa,
    output wire wo,
    output wire [1:0] woa,
    output logic lo,
    signed sn,
    output integer io,
    wire wn,
    output logic lr,
    [1:0] rni = '0,
    output logic ls,
    signed sni = '0,
    output logic lsr,
    signed [1:0] srni = '0,
    output logic lw,
    wire wni = '0,
    output logic lsn,
    signed [1:0] srn,
    output logic li,
    ib,
    output po,
    output var vo,
    output var [1:0] voa
);

  wire w;
  reg r;

  initial begin
    w = '0;  // Error
    o = '0;  // Error
    oa = '0;  // Error
    wo = '0;  // Error
    woa = '0;  // Error
    rn = '0;  // Error
    sn = '0;  // Error
    wn = '0;  // Error
    rni = '0;  // Error
    sni = '0;  // Error
    srni = '0;  // Error
    wni = '0;  // Error
    srn = '0;  // Error
    po = '0;  // Error
    r = '0;  // Not an error
    ro = '0;  // Not an error
    roa = '0;  // Not an error
    vo = '0;  // Not an error
    voa = '0;  // Not an error
    lo = '0;  // Not an error
    io = '0;  // Not an error
    lr = '0;  // Not an error
    ls = '0;  // Not an error
    lsr = '0;  // Not an error
    lw = '0;  // Not an error
    lsn = '0;  // Not an error
    li = '0;  // Not an error
    ib = '0;  // Not an error
  end

  logic rwv;
  sub sub (.rw(rwv));

endmodule

module sub (
    ref wire rw
);
  initial rw = '0;  // Error
endmodule
