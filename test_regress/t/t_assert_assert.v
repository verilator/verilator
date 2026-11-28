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
  int else_counts[5];
  int concurrent_else_counts[2];

  function automatic bit count_call(ref int calls);
    ++calls;
    return 1;
  endfunction

  initial begin
    int when_true, when_false;
    int fail_only, passed, failed, skipped;

    when_true = 0;
    when_false = 0;
    fail_only = 0;
    passed = 0;
    failed = 0;
    skipped = 0;

    // verilog_format: off
    for (int i = 0; i < 4; ++i) begin
      // The semicolon finishes the first assertion. The else belongs to the if.
      if (i[0])
        assert (count_call(when_true));
      else
        assert (count_call(when_false));

      if (i[0])
        assert #0 (1);
      else
        ++else_counts[0];
      if (i[0])
        assert final (1);
      else
        ++else_counts[1];
      if (i[0])
        assume (1);
      else
        ++else_counts[2];
      if (i[0])
        assume #0 (1);
      else
        ++else_counts[3];
      if (i[0])
        assume final (1);
      else
        ++else_counts[4];

      // An assertion can have a failure action alone, or both success and failure actions.
      assert (i[0]) else ++fail_only;
      if (i[1])
        assert (i[0]) ++passed; else ++failed;
      else
        ++skipped;
    end
    // verilog_format: on
    `checkd(when_true, 2);
    `checkd(when_false, 2);
    foreach (else_counts[i]) `checkd(else_counts[i], 2);
    `checkd(fail_only, 2);
    `checkd(passed, 1);
    `checkd(failed, 1);
    `checkd(skipped, 2);
  end

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
    // verilog_format: off
    if (cyc[0])
      assert property (1);
    else
      ++concurrent_else_counts[0];
    if (cyc[0])
      assume property (1);
    else
      ++concurrent_else_counts[1];
    // verilog_format: on
    if (cyc == 10) begin
      assert (cyc == 10);  // For debug to compare with other asserts
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
      foreach (concurrent_else_counts[i]) `checkd(concurrent_else_counts[i], 50);
      `checkd(cnt_tt, 10);
      `checkd(cnt_tf, 10);
      `checkd(cnt_ft, 19);
      `checkd(cnt_ff, 11);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
