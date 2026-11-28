// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2022 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  wire [3:0] a = 4'b11z1;
  logic b = 1'bz === a[1];
  logic c = 1'bz === a[2];
  logic d = 2'bzz === 2'(a[1]);
  logic e = 2'b0z === 2'(a[1]);

  bit [2:0] done = 3'b0;  // Set by each case below
  always begin
    wait (&done);
    if (b && !c && !d && e) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
    else begin
      $write("Error: b = %b, c = %b, d = %b, e = %b ", b, c, d, e);
      $write("expected: b = 1, c = 0, d = 0, e = 1\n");
      $stop;
    end
  end

  // An out-of-range variable select is X, not Z (IEEE 1800-2023 11.5.1)
  reg oe = 1'b0;
  wire [2:0] tn = oe ? 3'b010 : 3'bzzz;
  reg [1:0] idx = 2'd0;
  wire z = (tn[idx] === 1'bz);  // Tested directly
  reg pass = 1'b0;
  wire sel = pass ? tn[idx] : 1'bz;  // Driving another tristate net
  wire z_sel = (sel === 1'bz);
  wire [3:1] tnb = oe ? 3'b010 : 3'bzzz;  // Non-zero bound: idx 0 is out of range
  wire zb = (tnb[idx] === 1'bz);
  wire selb = pass ? tnb[idx] : 1'bz;
  wire z_selb = (selb === 1'bz);
  // verilator lint_off ASCRANGE
  wire [1:3] tna = oe ? 3'b010 : 3'bzzz;  // Ascending: idx 0 is out of range
  // verilator lint_on ASCRANGE
  wire za = (tna[idx] === 1'bz);
  wire sela = pass ? tna[idx] : 1'bz;
  wire z_sela = (sela === 1'bz);
  initial begin
    for (int o = 0; o < 2; o++) begin
      oe = o[0];
      for (int p = 0; p < 2; p++) begin
        pass = p[0];
        for (int i = 0; i < 4; i++) begin
          idx = i[1:0];
          #1;
          `checkd(z, (idx != 2'd3) & ~oe);
          `checkd(z_sel, ~pass | ((idx != 2'd3) & ~oe));
          `checkd(zb, (idx != 2'd0) & ~oe);
          `checkd(z_selb, ~pass | ((idx != 2'd0) & ~oe));
          `checkd(za, (idx != 2'd0) & ~oe);
          `checkd(z_sela, ~pass | ((idx != 2'd0) & ~oe));
        end
      end
    end
    done[0] = 1'b1;
  end

  // A side-effecting index, tested directly, is evaluated once
  reg sen = 1'b0;
  wire [2:0] stn = sen ? 3'b101 : 3'bz;
  int calls = 0;
  function automatic int sidx();
    ++calls;
    return 1;
  endfunction
  initial begin
    #1;
    `checkd(stn[sidx()] === 1'bz, 1);
    `checkd(calls, 1);
    sen = 1'b1;
    #1;
    `checkd(stn[sidx()] === 1'bz, 0);
    `checkd(calls, 2);
    done[1] = 1'b1;
  end

  // A side-effecting index, through other expressions, is evaluated once, and only when the
  // source evaluates it
  reg den = 1'b0;
  wire [2:0] dtn = den ? 3'b101 : 3'bz;
  logic [1:0] dlast;
  function automatic logic [1:0] dnet(input logic [1:0] i);
    dlast = i;
    return i;
  endfunction
  reg dpass = 1'b0;
  reg [1:0] di = 2'd0;
  wire dsel = dpass ? dtn[dnet(di)] : 1'bz;  // Driving another tristate net
  wire [1:0] dcat = {dtn[dnet(di)], 1'bz};  // Under a concatenation
  int dcalls = 0;
  function automatic int didx(input int i);
    ++dcalls;
    return i;
  endfunction
  logic dv;
  initial begin
    for (int o = 0; o < 2; o++) begin
      den = o[0];
      for (int i = 0; i < 4; i++) begin
        for (int p = 0; p < 2; p++) begin
          dpass = p[0];
          di = i[1:0];
          #1;
          `checkd(dsel === 1'bz, ~p[0] | ((i != 3) & ~den));
          `checkd(dcat[1] === 1'bz, (i != 3) & ~den);
          dcalls = 0;
          `checkd(p[0] && (dtn[didx(i)] === 1'bz), p[0] & (i != 3) & ~den);  // Short-circuited
          `checkd(dcalls, p);
          dcalls = 0;
          dv = p[0] ? dtn[didx(i)] : 1'bz;
          `checkd(dcalls, p);
        end
      end
    end
    done[2] = 1'b1;
  end
endmodule
