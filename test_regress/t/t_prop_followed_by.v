// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t (  /*AUTOARG*/
    // Inputs
    clk
);

  input clk;

  integer cyc = 0;

  // CRC pattern for non-vacuous match paths (lesson 33: 5+ bits OR'd).
  reg [63:0] crc = 64'h5aef0c8d_d70a4497;
  wire a = crc[0];
  wire b = crc[1];
  wire wide_ok = crc[2] | crc[3] | crc[4] | crc[5] | crc[6];

  always @(posedge clk) begin
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    if (cyc == 20) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  // --- Overlapped #-# (IEEE 1800-2023 16.12.9) ---
  // Both constants true: always passes.
  assert property (@(posedge clk) 1 #-# 1);

  // Guarded: when cyc > 5, (cyc > 3) and (cyc > 4) both hold.
  assert property (@(posedge clk) (cyc > 5) |-> ((cyc > 3) #-# (cyc > 4)));

  // --- Non-overlapped #=# (IEEE 1800-2023 16.12.9) ---
  // Guard first cycle so $past semantics are defined.
  assert property (@(posedge clk) (cyc > 1) |-> (1 #=# 1));

  // Guarded: when cyc > 3, $past(cyc>2) is true and (cyc>3) now.
  assert property (@(posedge clk) (cyc > 3) |-> ((cyc > 2) #=# (cyc > 3)));

  // --- Vacuous-guard wrap (from v1 harvested coverage) ---
  assert property (@(posedge clk) 0 |-> (0 #-# 0));
  assert property (@(posedge clk) 0 |-> (0 #=# 0));

  // --- CRC-random (lesson 17, 33): non-vacuous match path guaranteed ---
  // When wide_ok holds, b must hold -- a #-# wide_ok_or_b structure that
  // exercises both match and (guarded) fail branches across the CRC walk.
  assert property (@(posedge clk) (cyc > 2 && a) |-> (wide_ok #-# (wide_ok | b)));

endmodule
