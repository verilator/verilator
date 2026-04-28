// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Multi-dim iface arrays with ascending (left<right) ranges and negative
// indices.  The descending/zero-based case is covered by t_iface_array_multidim*;
// this test exercises the ascending() branch in V3Inst and negative lo() in
// name mangling.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

interface simple_if;
  logic [7:0] data;
endinterface

module t;
  // Both dims ascending, zero-based.
  simple_if asc[0:1][0:2] ();

  // Outer descending, inner ascending (mixed endianness).
  simple_if mix[1:0][0:2] ();

  // Negative indices: outer descending (1..-1), inner ascending (-2..0).
  simple_if neg[1:-1][-2:0] ();

  initial begin
    asc[0][0].data = 8'd10;
    asc[0][1].data = 8'd11;
    asc[0][2].data = 8'd12;
    asc[1][0].data = 8'd13;
    asc[1][1].data = 8'd14;
    asc[1][2].data = 8'd15;

    mix[0][0].data = 8'd20;
    mix[0][1].data = 8'd21;
    mix[0][2].data = 8'd22;
    mix[1][0].data = 8'd23;
    mix[1][1].data = 8'd24;
    mix[1][2].data = 8'd25;

    neg[-1][-2].data = 8'd50;
    neg[-1][-1].data = 8'd51;
    neg[-1][0].data = 8'd52;
    neg[0][-2].data = 8'd53;
    neg[0][-1].data = 8'd54;
    neg[0][0].data = 8'd55;
    neg[1][-2].data = 8'd56;
    neg[1][-1].data = 8'd57;
    neg[1][0].data = 8'd58;
  end

  initial begin
    #1;
    `checkd(asc[0][0].data, 8'd10);
    `checkd(asc[0][1].data, 8'd11);
    `checkd(asc[0][2].data, 8'd12);
    `checkd(asc[1][0].data, 8'd13);
    `checkd(asc[1][1].data, 8'd14);
    `checkd(asc[1][2].data, 8'd15);

    `checkd(mix[0][0].data, 8'd20);
    `checkd(mix[0][1].data, 8'd21);
    `checkd(mix[0][2].data, 8'd22);
    `checkd(mix[1][0].data, 8'd23);
    `checkd(mix[1][1].data, 8'd24);
    `checkd(mix[1][2].data, 8'd25);

    `checkd(neg[-1][-2].data, 8'd50);
    `checkd(neg[-1][-1].data, 8'd51);
    `checkd(neg[-1][0].data, 8'd52);
    `checkd(neg[0][-2].data, 8'd53);
    `checkd(neg[0][-1].data, 8'd54);
    `checkd(neg[0][0].data, 8'd55);
    `checkd(neg[1][-2].data, 8'd56);
    `checkd(neg[1][-1].data, 8'd57);
    `checkd(neg[1][0].data, 8'd58);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
