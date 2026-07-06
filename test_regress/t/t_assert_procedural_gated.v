// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// IEEE 1800-2023 16.14.6: if-gated procedural concurrent assertion vs
// module-scope reference; counts must diverge to prove the gate is preserved.

module t (
    input clk
);

  int cyc;
  reg [63:0] crc;
  reg rst_l;

  // Derive property operands from non-adjacent CRC bits.
  wire [1:0] req = {crc[6], crc[0]};
  wire gnt = crc[12];

  int count_gated = 0;
  int count_ref = 0;

  // Procedural concurrent assertion with inferred clock, guarded by
  // `if (cyc[0])`. The assertion attempt only starts on odd cycles.
  always @(negedge clk) begin
    if (cyc[0])
      assert property (disable iff (!rst_l) ((&req) |-> gnt))
      else count_gated <= count_gated + 1;
  end

  // Module-scope reference assertion with identical disable iff / property
  // but no procedural gating.
  assert property (@(negedge clk) disable iff (!rst_l) ((&req) |-> gnt))
  else count_ref <= count_ref + 1;

  always @(posedge clk) begin
`ifdef TEST_VERBOSE
    $write("[%0t] cyc==%0d crc=%x rst_l=%b req=%b gnt=%b gated=%0d ref=%0d\n", $time, cyc, crc,
           rst_l, req, gnt, count_gated, count_ref);
`endif
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    if (cyc == 0) begin
      crc <= 64'h5aef0c8d_d70a4497;
      rst_l <= 1'b0;
    end
    else if (cyc == 3) begin
      rst_l <= 1'b1;
    end
    else if (cyc == 99) begin
      `checkh(crc, 64'hc77bb9b3784ea091);
      `checkd(count_gated, 5);  // Other sims same, one other: 4
      `checkd(count_ref, 12);  // Other sims same, one other: 10
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
