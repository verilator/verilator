// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Nikolai Kumar
// SPDX-License-Identifier: CC0-1.0

module t;
  int x;
  int pass_count, fail_count;

  initial begin
    pass_count = 0;
    fail_count = 0;

    assert((std::randomize(x) with {x inside {10, 20}; }) == 1)
      pass_count++;
    else
      assert((std::randomize(x) with {x inside {1, 2}; }) == 1)
      fail_count++; //Should not run

    assert((std::randomize(x) with {x > 100; x inside {1, 2 , 3}; }) == 1)
      pass_count++; //Should not run
    else
      assert((std::randomize(x) with {x inside {40, 50}; }) == 1)
      fail_count++;

    if (pass_count != 1) begin
      $display("FAIL: pass_count=%0d expected 1", pass_count);
      $stop;
    end
    if (fail_count != 1) begin
      $display("FAIL: fail_count=%0d expected 1", fail_count);
      $stop;
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
