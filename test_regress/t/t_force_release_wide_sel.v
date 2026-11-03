// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Michael Bedford Taylor
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

module t (
    input clk
);
  typedef struct packed {
    logic [99:0] hi;
    logic [6:0] f;
    logic [92:0] lo;
  } s_t;

  integer cyc = 0;
  logic [199:0] w;
  s_t s;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 0) begin
      w <= '0;
      s <= '0;
    end
    else if (cyc == 1) begin
      force w[3] = 1'b1;
      force w[47:40] = 8'ha5;
      force w[130:91] = 40'h12_3456_789a;
      force w[199:131] = '1;
      force s.f = 7'h55;
    end
    else if (cyc == 2) begin
      // Not continuously driven, so each released range keeps its forced value
      release w[3];
      release w[47:40];
      release w[130:91];
      release w[199:131];
      release s.f;
    end
    else if (cyc == 3) begin
      `checkh(w[3], 1'b1);
      `checkh(w[47:40], 8'ha5);
      `checkh(w[130:91], 40'h12_3456_789a);
      `checkh(w[199:131], {69{1'b1}});
      `checkh(w[2:0], 3'h0);
      `checkh(w[39:4], 36'h0);
      `checkh(w[90:48], 43'h0);
      `checkh(s.f, 7'h55);
      `checkh(s.hi, 100'h0);
      `checkh(s.lo, 93'h0);
      w[47:40] <= 8'h0f;
      s.f <= 7'h01;
    end
    else if (cyc == 4) begin
      `checkh(w[47:40], 8'h0f);
      `checkh(w[130:91], 40'h12_3456_789a);
      `checkh(s.f, 7'h01);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
