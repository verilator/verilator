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
  reg [63:0] crc = 64'h5aef0c8d_d70a4497;
  wire a = crc[0];
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

  // Duality: #-# / #=# non-vacuously fail on antecedent miss; |-> / |=> vacuously pass.
  assert property (@(posedge clk) a #-# 1'b1)
  else ovl_f = ovl_f + 1;
  assert property (@(posedge clk) a #=# 1'b1)
  else novl_f = novl_f + 1;
  assert property (@(posedge clk) a |-> 1'b1)
  else impl_f = impl_f + 1;
  assert property (@(posedge clk) a |=> 1'b1)
  else nimp_f = nimp_f + 1;

  // Antecedent-implies-self consequent: never fails on any cycle.
  assert property (@(posedge clk) wide |-> (wide #-# wide))
  else wide_f = wide_f + 1;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    if (cyc == 32) begin
      // Counts are deterministic for this CRC seed; Questa reference run
      // (IEEE 1800-2023 16.12.9) reports ovl=19, novl=19 -- a 1-cycle
      // preponed-sampling delta vs Verilator.
      $display("ovl=%0d novl=%0d impl=%0d nimp=%0d wide=%0d", ovl_f, novl_f, impl_f, nimp_f,
               wide_f);
      if (ovl_f != 20) $stop;
      if (novl_f != 20) $stop;
      if (impl_f != 0) $stop;
      if (nimp_f != 0) $stop;
      if (wide_f != 0) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
