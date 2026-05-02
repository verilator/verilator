// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// verilog_format: off
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);
// verilog_format: on

module t;

  localparam int COUNT = 1000;

  int seq;
  int counts[8];
  int sum, hits;

  task prep();
    for (int i = 0; i < COUNT; ++i) counts[i] = 0;
  endtask

  initial begin
    // Single-port and no-port productions
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

    // Multi-port, repeat-with-arg, if-prod-with-arg, nested-prod-with-arg
    sum  = 0;
    hits = 0;
    for (int i = 0; i < COUNT; ++i) begin
      // verilog_format: off
      randsequence(main)
        main : multi nested ifcall reps;
        multi : add2(3, 4);
        nested : leaf(7);
        ifcall : if (1) add2(1, 2) else add2(0, 0);
        reps : repeat (3) add2(2, 0);
        void add2(int a, int b) : { sum = sum + a + b; hits = hits + 1; };
        void leaf(int v) : { sum = sum + v; hits = hits + 1; };
      endsequence
      // verilog_format: on
    end
    `checkd(sum, COUNT * (7 + 7 + 3 + 3 * 2));
    `checkd(hits, COUNT * (1 + 1 + 1 + 3));

    // Default port values (IEEE 1800-2023 18.17.7)
    sum  = 0;
    hits = 0;
    for (int i = 0; i < COUNT; ++i) begin
      // verilog_format: off
      randsequence(main)
        main : useDefault override1 override2;
        useDefault : add_def;
        override1 : add_def(50);
        override2 : add_def(100);
        void add_def(int n = 7) : { sum = sum + n; hits = hits + 1; };
      endsequence
      // verilog_format: on
    end
    `checkd(sum, COUNT * (7 + 50 + 100));
    `checkd(hits, COUNT * 3);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
