// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2025 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// verilog_format: off
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);
// verilog_format: on

module t;

  localparam int COUNT = 1000;

  int seq;
  int counts[8];

  task prep();
    for (int i = 0; i < COUNT; ++i) counts[i] = 0;
  endtask

  initial begin
    // functions
    prep();
    for (int i = 0; i < COUNT; ++i) begin
      randsequence(main)
        main: f_1 f_2 f_3;
        f_1 : func(10);
        f_2 : func(20);
        f_3 : fnoarg;
        void func(int n) : { counts[1] += n; };
        void fnoarg : { ++counts[2]; };
      endsequence
    end
    `checkd(counts[1], COUNT * (10 + 20));
    `checkd(counts[2], COUNT * 1 / 1);  // return

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
