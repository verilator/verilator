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

module t (
    input clk
);

  logic [63:0] crc = 64'h5aef0c8dd70a4497;
  logic rst_n = 1'b0;
  logic a, b, c, d, e;
  int cyc = 0;

  int hit_simple = 0;
  int hit_clocked = 0;
  int hit_clocked_disable = 0;
  int hit_default_disable = 0;
  int hit_consrep_range = 0;
  int hit_consrep_2 = 0;
  int hit_consrep_3 = 0;

  default clocking cb @(posedge clk);
  endclocking

  // Non-adjacent CRC bits to avoid LFSR shift correlation
  assign a = crc[0];
  assign b = crc[5];
  assign c = crc[10];
  assign d = crc[15];
  assign e = crc[20];

  // Form 1: cover sequence ( sexpr ) stmt  -- default clocking, no disable
  cover sequence (a | b | c | d | e) hit_simple++;

  // Form 2: cover sequence ( clocking_event sexpr ) stmt  -- explicit clock,
  // bounded range delay (the case where IEEE "every end-of-match" diverges
  // from cover_property's "one match per attempt" semantics)
  cover sequence (@(posedge clk) (a | b | c | d | e) ##[1:3] b) hit_clocked++;

  // Form 3: cover sequence ( clocking_event disable iff (expr) sexpr ) stmt
  cover sequence (@(posedge clk) disable iff (!rst_n) a ##1 b) hit_clocked_disable++;

  // Form 4: cover sequence ( disable iff (expr) sexpr ) stmt  -- default clock
  cover sequence (disable iff (!rst_n) a ##1 c) hit_default_disable++;

  // Form 5: consecutive repetition (per-end-of-match). A ranged repetition
  // a[*2:3] ends every cycle a 2- or 3-run completes; by IEEE 1800-2023 16.9.2
  // a[*2:3] == a[*2] or a[*3], so the range count equals the sum of the two
  // fixed counts -- a Questa-free identity that validates the multiplicity.
  cover sequence (a [* 2: 3]) hit_consrep_range++;
  cover sequence (a [* 2]) hit_consrep_2++;
  cover sequence (a [* 3]) hit_consrep_3++;

  always @(posedge clk) begin
`ifdef TEST_VERBOSE
    $write("[%0t] cyc=%0d crc=%x a=%b b=%b c=%b d=%b e=%b\n", $time, cyc, crc, a, b, c, d, e);
`endif
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[1] ^ crc[0]};
    if (cyc == 2) rst_n <= 1'b1;
    if (cyc == 99) begin
      `checkh(crc, 64'h261a9f1371d7aadf);
      `checkd(hit_simple, 96);  // Questa:  95 (single-sexpr sample-edge diff)
      `checkd(hit_clocked, 149);  // IEEE 16.14.3: every end-of-match
      `checkd(hit_clocked_disable, 28);  // Questa:  27 (sample-edge diff, ##1 single delay)
      `checkd(hit_default_disable, 30);  // Questa:  30
`ifdef TEST_VERBOSE
      $write("consrep range=%0d  2=%0d  3=%0d  sum=%0d\n", hit_consrep_range, hit_consrep_2,
             hit_consrep_3, hit_consrep_2 + hit_consrep_3);
`endif
      `checkd(hit_consrep_2, 30);
      `checkd(hit_consrep_3, 14);
      // IEEE 1800-2023 16.9.2: a[*2:3] == a[*2] or a[*3], so the per-end counts add.
      `checkd(hit_consrep_range, hit_consrep_2 + hit_consrep_3);  // == 44
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
