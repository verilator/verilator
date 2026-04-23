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

  // --- Smoke (compile + trivially pass) ---
  assert property (@(posedge clk) 1'b1 #-# 1'b1);
  assert property (@(posedge clk) 0 |-> (0 #-# 0));
  assert property (@(posedge clk) 0 |-> (0 #=# 0));

  // --- CRC-driven match paths (lesson 33) ---
  // Overlapped: when wide_ok holds, (wide_ok #-# wide_ok) holds at the same cycle.
  assert property (@(posedge clk) wide_ok |-> (wide_ok #-# wide_ok));
  // Non-overlapped: weak #=# with body 1'b1 reduces to the antecedent holding now.
  assert property (@(posedge clk) wide_ok |-> (wide_ok #=# 1'b1));
  // Nested followed-by inside implication consequent.
  assert property (@(posedge clk) (cyc > 5) |-> ((cyc > 3) #-# (cyc > 4)));

  // --- Duality: #-#/#=# non-vacuously fail on antecedent miss, |->/|=> vacuously pass ---
  // `a` is a CRC bit (~50% high). Four top-level attempts per posedge share the
  // same antecedent; reject-sink fires on followed-by when a==0, never on implication.
  integer n_ovl_fails = 0;
  integer n_novl_fails = 0;
  integer n_impl_fails = 0;
  integer n_nimp_fails = 0;

  assert property (@(posedge clk) a #-# 1'b1)
      else n_ovl_fails = n_ovl_fails + 1;
  assert property (@(posedge clk) a #=# 1'b1)
      else n_novl_fails = n_novl_fails + 1;
  assert property (@(posedge clk) a |-> 1'b1)
      else n_impl_fails = n_impl_fails + 1;
  assert property (@(posedge clk) a |=> 1'b1)
      else n_nimp_fails = n_nimp_fails + 1;

  final begin
    $display("ovl=%0d novl=%0d impl=%0d nimp=%0d",
             n_ovl_fails, n_novl_fails, n_impl_fails, n_nimp_fails);
    if (n_ovl_fails == 0) $fatal(1, "#-# reject-sink never fired");
    if (n_novl_fails == 0) $fatal(1, "#=# reject-sink never fired");
    if (n_impl_fails != 0) $fatal(1, "|-> should vacuously pass, got %0d fails", n_impl_fails);
    if (n_nimp_fails != 0) $fatal(1, "|=> should vacuously pass, got %0d fails", n_nimp_fails);
  end

endmodule
