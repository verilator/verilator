// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: got=%p exp=%p (%s !== %s)\n", `__FILE__, `__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while (0);
// verilog_format: on

// The number of clocks in the clock vector

localparam int N = 5;

`ifdef LIB_CREATE
// This is built with --lib-create

module sub (
    input logic [N-1:0] clkvec,
    output logic [7:0] cnt[N],
    input logic [6:0] din,
    inout wire [6:0] bus_z,
    inout wire [6:0] bus_a,
    output wire [6:0] seen
);

  assign bus_z = clkvec[0] ? din : 7'bz;
  assign bus_a = clkvec[1] ? (din ^ 7'h55) : 7'bz;
  assign seen = bus_z ^ {bus_a[5:0], bus_a[6]};

  for (genvar i = 0; i < N; ++i) begin : GEN
    logic [7:0] counter = 8'd0;
    always @(posedge clkvec[i]) counter <= counter + 8'd1;
    assign cnt[i] = counter;
  end

endmodule

`else
// This is built as the top level

module top;

  logic [N-1:0] clkvec = N'(0);
  logic [7:0] cnt[N];
  logic [7:0] cnt_pos[N];
  wire [6:0] a_en, a_out, z_en, z_out, seen;
  wire [6:0] a_en_pos, a_out_pos, z_en_pos, z_out_pos, seen_pos;

  // Generate clocks by rotation
  always #5 clkvec = {clkvec[N-2:0], clkvec[N-1] | ~|clkvec};

  sub sub_i (
      .clkvec(clkvec),
      .cnt(cnt),
      .din(7'h35),
      .bus_z(7'h27),
      .bus_a(7'h14),
      .seen(seen),
      .bus_a__en(a_en),
      .bus_a__out(a_out),
      .bus_z__en(z_en),
      .bus_z__out(z_out)
  );

  // Exercise positional connections as well as named ones. Generated ports
  // precede source ports, which retain their declaration order.
  sub sub_pos (
      a_en_pos,
      a_out_pos,
      z_en_pos,
      z_out_pos,
      clkvec,
      cnt_pos,
      7'h35,
      7'h27,
      7'h14,
      seen_pos
  );

  always @(clkvec) begin
    #1;
    `checkh(seen, 7'h0f);
    `checkh(seen_pos, seen);
    `checkh(z_en, {7{clkvec[0]}});
    `checkh(a_en, {7{clkvec[1]}});
    `checkh(z_en_pos, z_en);
    `checkh(a_en_pos, a_en);
    if (clkvec[0]) `checkh(z_out, 7'h35);
    if (clkvec[1]) `checkh(a_out, 7'h60);
    if (clkvec[0]) `checkh(z_out_pos, z_out);
    if (clkvec[1]) `checkh(a_out_pos, a_out);
    $write("%10t %05b", $time, clkvec);
    for (int i = N - 1; i >= 0; --i) begin
      `checkh(cnt_pos[i], cnt[i]);
      $write(" cnt[%0d]=%02d", i, cnt[i]);
    end
    $write("\n");

    // No counter should reach above 10
    for (int i = 0; i < N; ++i) begin
      if (cnt[i] > 10) $stop;
    end

    // Conclude when all counters reach 10
    begin
      automatic bit done = 1'b1;
      for (int i = 0; i < N; ++i) begin
        if (cnt[i] != 10) done = 1'b0;
      end
      if (done) begin
        $write("*-* All Finished *-*\n");
        $finish;
      end
    end
  end

endmodule

`endif
