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

  int cyc = 0;

  reg [2:0] value = 0;

  int cnt_tt = 0;
  int cnt_tf = 0;
  int cnt_ft = 0;
  int cnt_ff = 0;

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
      `checkd(cnt_tt, 10);
      `checkd(cnt_tf, 10);
      `checkd(cnt_ft, 19);
      `checkd(cnt_ff, 11);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
