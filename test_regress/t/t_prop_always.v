// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

  bit clk = 0;
  always #5 clk = ~clk;

  bit [63:0] crc = 64'h5aef0c8d_d70a4497;
  int        cyc = 0;
  logic      a;

  assign a = crc[0];

  always @(posedge clk) begin
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    if (cyc == 99) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  int unbounded_pass = 0;
  int unbounded_fail = 0;
  int bounded_pass = 0;
  int bounded_fail = 0;
  int sbounded_pass = 0;
  int sbounded_fail = 0;
  int degenerate_pass = 0;
  int degenerate_fail = 0;

  assert property (@(posedge clk) always 1'b1)
    unbounded_pass++;
  else
    unbounded_fail++;

  assert property (@(posedge clk) always [0:3] a)
    bounded_pass++;
  else
    bounded_fail++;

  assert property (@(posedge clk) s_always [1:2] a)
    sbounded_pass++;
  else
    sbounded_fail++;

  assert property (@(posedge clk) always [0:0] a)
    degenerate_pass++;
  else
    degenerate_fail++;

  property p_always_true;
    @(posedge clk) always (1'b1);
  endproperty
  assert property (p_always_true);

  final begin
    $display("unbounded_pass=%0d fail=%0d", unbounded_pass, unbounded_fail);
    $display("bounded_pass=%0d fail=%0d", bounded_pass, bounded_fail);
    $display("sbounded_pass=%0d fail=%0d", sbounded_pass, sbounded_fail);
    $display("degenerate_pass=%0d fail=%0d", degenerate_pass, degenerate_fail);
    if (unbounded_pass != 100 || unbounded_fail != 0) $fatal(1, "unbounded counts wrong");
    if (bounded_pass != 3 || bounded_fail != 97) $fatal(1, "bounded counts wrong");
    if (sbounded_pass != 23 || sbounded_fail != 76) $fatal(1, "sbounded counts wrong");
    if (degenerate_pass + degenerate_fail != 100) $fatal(1, "degenerate total wrong");
  end

endmodule
