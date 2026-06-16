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

  // Form 1: cover sequence ( sexpr ) stmt
  cover sequence (a | b | c | d | e) hit_simple++;

  // Form 2: cover sequence ( clocking_event sexpr ) stmt
  cover sequence (@(posedge clk) (a | b | c | d | e) ##[1:3] b) hit_clocked++;

  // Form 3: cover sequence ( clocking_event disable iff (expr) sexpr ) stmt
  cover sequence (@(posedge clk) disable iff (!rst_n) a ##1 b) hit_clocked_disable++;

  // Form 4: cover sequence ( disable iff (expr) sexpr ) stmt
  cover sequence (disable iff (!rst_n) a ##1 c) hit_default_disable++;

  // Form 5: consecutive repetition, counted per end-of-match
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
      $finish;
    end
  end

  // Read the counters in 'final', not the clocked block: a same-cycle read of a
  // cover counter races the cover's increment under --threads (vltmt). Verilator
  // counts one more end-of-match than Questa 2022.3 on some forms at the
  // simulation boundary; the Questa value is noted per check.
  final begin
`ifdef TEST_VERBOSE
    $write("simple=%0d clocked=%0d clk_dis=%0d def_dis=%0d range=%0d 2=%0d 3=%0d\n", hit_simple,
           hit_clocked, hit_clocked_disable, hit_default_disable, hit_consrep_range, hit_consrep_2,
           hit_consrep_3);
`endif
    `checkd(hit_simple, 96);  // Questa: 95
    `checkd(hit_clocked, 149);  // Questa: 149
    `checkd(hit_clocked_disable, 28);  // Questa: 27
    `checkd(hit_default_disable, 30);  // Questa: 30
    `checkd(hit_consrep_2, 30);  // Questa: 29
    `checkd(hit_consrep_3, 14);  // Questa: 13
    // a[*2:3] == a[*2] or a[*3] (IEEE 1800-2023 16.9.2)
    `checkd(hit_consrep_range, hit_consrep_2 + hit_consrep_3);  // 44; Questa: 42
    $write("*-* All Finished *-*\n");
  end
endmodule
