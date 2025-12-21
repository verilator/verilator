// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  bit toggle = 0;
  int inc = 0;
  int dec = 0;

  assert property (@(negedge clk) not toggle)
  else ++inc;

  assert property (@(negedge clk) not toggle)
  else --dec;

  int passsInc = 0;
  int passsDec = 0;

  assert property (@(negedge clk) not toggle) ++passsInc;
  else --passsDec;

  assert property (@(negedge clk) not toggle) ++passsInc;
  cover property (@(negedge clk) not toggle) ++passsInc;

  int inc2 = 0;
  assert property (@(e) not toggle) begin
    `checkh(inc2, 0);
    inc2++;
    `checkh(inc2,1);
  end
  event e;

  int cyc = 0;

  always @(posedge clk) begin
`ifdef TEST_VERBOSE
    $write("[%0t] cyc==%0d toggle==%d\n", $time, cyc, toggle);
`endif
    if (cyc % 3 == 0) begin
      toggle <= 1;
    end
    else begin
      toggle <= 0;
    end

    cyc <= cyc + 1;

    if (cyc == 5) begin
      ->e;
      `checkh(inc, 2);
      `checkh(dec, -2);
      `checkh(passsInc, 6);
      `checkh(passsDec, -2);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
