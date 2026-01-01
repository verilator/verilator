// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2023 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// verilog_format: off
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);
`define check_range(gotv,minv,maxv) do if ((gotv) < (minv) || (gotv) > (maxv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d-%0d\n", `__FILE__,`__LINE__, (gotv), (minv), (maxv)); $stop; end while(0);
`define check_within_30_percent(gotv,val) `check_range((gotv), (val) * 70 / 100, (val) * 130 / 100)
// verilog_format: on

module t;

  localparam int COUNT = 1000;

  int x;
  int seq;
  int counts[8];

  task prep();
    for (int i = 0; i < COUNT; ++i) counts[i] = 0;
  endtask

  initial begin
    prep();

    // rand join
    x = 0;
    randsequence(main)
      main : rand join first second;
      first : { x = x + 20; };
      second : { x = x - 9; } { x = x - 1; };
    endsequence
    `checkd(x, 10);

    prep();
    for (int i = 0; i < COUNT; ++i) begin
      randsequence(main)
        main: rand join count_1 count_2;
        count_1: { ++counts[1]; };
        count_2: { ++counts[2]; };
      endsequence
    end
    `check_within_30_percent(counts[1], COUNT * 1 / 1);
    `check_within_30_percent(counts[2], COUNT * 1 / 1);

    // rand join weight (TODO weight not tested yet)
    prep();
    for (int i = 0; i < COUNT; ++i) begin
      randsequence(main)
        main: rand join (1.0) count_1 count_2;
        count_1: { ++counts[1]; };
        count_2: { ++counts[2]; };
      endsequence
      randsequence(main)
        main: rand join (0.0) count_3 count_4;
        count_3: { ++counts[3]; };
        count_4: { ++counts[4]; };
      endsequence
    end
    `check_within_30_percent(counts[1], COUNT * 1 / 1);
    `check_within_30_percent(counts[2], COUNT * 1 / 1);
    `check_within_30_percent(counts[3], COUNT * 1 / 1);
    `check_within_30_percent(counts[4], COUNT * 1 / 1);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
