// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Bitblasting of packed variables marked with split_var. Variables expected to be split are
// marked with a 'Split N' comment, where N is the number of fragments.

module t (
    input clk
);

  int cyc = 0;
  logic [63:0] crc = 64'h5aef0c8d_d70a4497;
  logic [63:0] crc_q = '0;

  // Written whole from a constant select, then partially, read spanning fragments
  logic [7:0] x  /*verilator split_var*/;  // Split 3
  // Blocking swap reading the variable assigned whole, through a temporary
  logic [7:0] sw  /*verilator split_var*/;  // Split 2
  // Non-blocking, written whole from a constant select, and partially
  logic [7:0] nb  /*verilator split_var*/;  // Split 2
  // Written whole from a constant, then partially
  logic [7:0] wk  /*verilator split_var*/;  // Split 2
  // Written whole from a variable, then partially
  logic [7:0] wv  /*verilator split_var*/;  // Split 2
  logic [7:0] src;
  // Read whole as an assignment RHS
  logic [7:0] wr  /*verilator split_var*/;  // Split 2
  logic [7:0] wrc;
  // Written and read hierarchically, see 'subh'
  subh u_h ();

  always_comb begin
    x = crc[7:0];
    x[3:2] = x[5:4];
  end

  always_comb begin
    sw[3:0] = crc[3:0];
    sw[7:4] = crc[7:4];
    sw = {sw[3:0], sw[7:4]};
  end

  always_ff @(posedge clk) begin
    nb <= crc[7:0];
    nb[0] <= crc[8];
  end

  always_comb begin
    wk = '0;
    wk[0] = crc[0];
  end

  assign src = crc[15:8];
  always_comb begin
    wv = src;
    wv[7] = crc[1];
  end

  assign wr[3:0] = crc[3:0];
  assign wr[7:4] = crc[7:4];
  assign wrc = wr;

  assign u_h.h[3:0] = crc[3:0];

  always @(posedge clk) begin
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    crc_q <= crc;
    `checkh(x[7:1], {crc[7:4], crc[5:4], crc[1]});
    `checkh({sw[7:4], sw[3:0]}, {crc[3:0], crc[7:4]});
    if (cyc > 0) `checkh({nb[7:1], nb[0]}, {crc_q[7:1], crc_q[8]});
    `checkh(wk, {7'b0, crc[0]});
    `checkh(wv, {crc[1], crc[14:8]});
    `checkh(wrc, crc[7:0]);
    `checkh(u_h.h, {crc[3:0] ^ crc[7:4], crc[3:0]});
    if (cyc == 99) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule

module subh;
  logic [7:0] h  /*verilator split_var*/;  // Split 2

  assign h[7:4] = h[3:0] ^ t.crc[7:4];
endmodule
