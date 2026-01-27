// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  int cyc;

  reg [2:0] value;

  int cnt_tt;
  int cnt_tf;
  int cnt_ft;
  int cnt_ff;

  assert property (@(negedge clk) disable iff (value[1]) value[2]) begin
    assert (value[0]) ++cnt_tt;
    else ++cnt_tf;
  end
  else begin
    assert (value[0]) ++cnt_ft;
    else ++cnt_ff;
  end

  // Test loop
  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 10) begin
      assert(cyc == 10);  // For debug to compare with other asserts
      value <= 0;
      cnt_tt = 0;
      cnt_tf = 0;
      cnt_ft = 0;
      cnt_ff = 0;
    end
    else if (cyc > 10 && cyc < 90) begin
      value <= cyc[2:0];
    end
    else if (cyc == 99) begin
      `checkd(cnt_tt, 10);
      `checkd(cnt_tf, 10);
      `checkd(cnt_ft, 19);
      `checkd(cnt_ff, 11);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
