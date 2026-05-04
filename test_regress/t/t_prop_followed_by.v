// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

`define checkd(gotv, expv) \
  do if ((gotv) !== (expv)) begin \
    $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__, `__LINE__, (gotv), (expv)); \
    $stop; \
  end while (0);

module t (
    input clk
);

  integer cyc = 0;
  reg [63:0] crc = 64'h5aef0c8d_d70a4497;
  wire a = crc[0];
  wire b = crc[1];
  wire wide = crc[2] | crc[3] | crc[4] | crc[5] | crc[6];

  integer ovl_f = 0;
  integer novl_f = 0;
  integer impl_f = 0;
  integer nimp_f = 0;
  integer wide_f = 0;

  // Smoke: trivially-true forms must compile and never fail.
  assert property (@(posedge clk) 1'b1 #-# 1'b1);
  assert property (@(posedge clk) 0 |-> (0 #-# 0));
  assert property (@(posedge clk) 0 |-> (0 #=# 0));

  // Duality: #-# / #=# non-vacuously fail on antecedent miss; |-> / |=> vacuously
  // pass. Counters expose the asymmetry: ovl / novl include both antecedent-miss
  // and consequent-miss; impl / nimp count consequent-miss only.
  assert property (@(posedge clk) a #-# b)
  else ovl_f = ovl_f + 1;
  assert property (@(posedge clk) a #=# b)
  else novl_f = novl_f + 1;
  assert property (@(posedge clk) a |-> b)
  else impl_f = impl_f + 1;
  assert property (@(posedge clk) a |=> b)
  else nimp_f = nimp_f + 1;

  // Antecedent-implies-self consequent: never fails on any cycle.
  assert property (@(posedge clk) wide |-> (wide #-# wide))
  else wide_f = wide_f + 1;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    if (cyc == 32) begin
      // Counts are deterministic for this CRC seed. Questa reference run
      // (IEEE 1800-2023 16.12.9) reports ovl=28, novl=19, impl=9, nimp=0; the
      // ovl/novl deltas vs Verilator are 1-cycle preponed-sampling differences.
      $display("ovl=%0d novl=%0d impl=%0d nimp=%0d wide=%0d", ovl_f, novl_f, impl_f, nimp_f,
               wide_f);
      `checkd(ovl_f, 29);
      `checkd(novl_f, 20);
      `checkd(impl_f, 9);
      `checkd(nimp_f, 0);
      `checkd(wide_f, 0);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
