// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2023 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define check_range(gotv,minv,maxv) do if ((gotv) < (minv) || (gotv) > (maxv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d-%0d\n", `__FILE__,`__LINE__, (gotv), (minv), (maxv)); `stop; end while(0);
`define check_within_30_percent(gotv,val) `check_range((gotv), (val) * 70 / 100, (val) * 130 / 100)

module t(/*AUTOARG*/);

   localparam int COUNT = 1000;

   int seq;
   int counts[8];

   function automatic int sfunc();
      int o = 2;
      randsequence(main)
         main : one;
         one : { o = 1; };
      endsequence
      return o;
   endfunction

   task prep();
      for (int i = 0; i < COUNT; ++i) counts[i] = 0;
   endtask

   initial begin;
      if (sfunc() != 1) $stop;

      // simple
      prep();
      seq = 0;
      randsequence(main)
         main: one two three;
         two: { `checkd(seq, 1); seq = 2; };
         one: { `checkd(seq, 0); seq = 1; };
         three: { `checkd(seq, 2); seq = 3; };
      endsequence
      `checkd(seq, 3);

      // simple unnamed
      prep();
      seq = 0;
      randsequence()
         unnamed: { seq = 2; };
      endsequence
      `checkd(seq, 2);

      // empty block
      prep();
      randsequence()
         unnamed: { };
      endsequence

      // weight
      prep();
      for (int i = 0; i < COUNT; ++i) begin
         randsequence(main)
            main: one | two | three := 2;
            one: { ++counts[0]; };
            two: { ++counts[1]; };
            three: { ++counts[2]; };
         endsequence
      end
      `check_within_30_percent(counts[0], COUNT * 1 / 4);
      `check_within_30_percent(counts[1], COUNT * 1 / 4);
      `check_within_30_percent(counts[2], COUNT * 2 / 4);

      // case
      prep();
      for (int i = 0; i < COUNT; ++i) begin
         randsequence(main)
            main: one_if;
            one_if: if (i % 10 == 0) count_1 else most;
            count_1: { ++counts[1]; };
            count_2: { ++counts[2]; };
            count_3: { ++counts[3]; };
            count_4: { ++counts[4]; };
            bad: { $stop; };
            most: case (i % 10)
                    0: bad;
                    1, 2: count_2;
                    3, 4, 5: count_3;
                    default: count_4;
                  endcase;
         endsequence
      end
      `check_within_30_percent(counts[1], COUNT * 1 / 10);
      `check_within_30_percent(counts[2], COUNT * 2 / 10);
      `check_within_30_percent(counts[3], COUNT * 3 / 10);
      `check_within_30_percent(counts[4], COUNT * 4 / 10);

      // case - different default
      prep();
      for (int i = 0; i < COUNT; ++i) begin
         randsequence(main)
            main: one_if;
            one_if: if (i % 10 == 0) count_1 else most;
            count_1: { ++counts[1]; };
            count_2: { ++counts[2]; };
            count_3: { ++counts[3]; };
            count_4: { ++counts[4]; };
            bad: { $stop; };
            most: case (i % 10)
                    0: bad;
                    1, 2: count_2;
                    3, 4, 5: count_3;
                    default count_4;  // No :
                  endcase;
         endsequence
      end
      `check_within_30_percent(counts[1], COUNT * 1 / 10);
      `check_within_30_percent(counts[2], COUNT * 2 / 10);
      `check_within_30_percent(counts[3], COUNT * 3 / 10);
      `check_within_30_percent(counts[4], COUNT * 4 / 10);

      // repeat
      prep();
      randsequence(main)
         main: repeat(10) count_1;
         count_1: { ++counts[1]; };
      endsequence
      `checkd(counts[1], 10);

      // rand join
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

      // break
      prep();
      for (int i = 0; i < COUNT; ++i) begin
         automatic bit fiftyfifty = i[0];
         randsequence(main)
            main: count_1 check count_2;
            check: count_3 { if (fiftyfifty) break; } count_4;
            count_1: { ++counts[1]; };
            count_2: { ++counts[2]; };
            count_3: { ++counts[3]; };
            count_4: { ++counts[4]; };
         endsequence
      end
      `checkd(counts[1], COUNT * 1 / 1);
      `checkd(counts[2], COUNT * 1 / 2);  // break
      `checkd(counts[3], COUNT * 1 / 1);
      `checkd(counts[4], COUNT * 1 / 2);  // break or return

      // return
      prep();
      for (int i = 0; i < COUNT; ++i) begin
         automatic bit fiftyfifty = i[0];
         randsequence(main)
            main: count_1 check count_2;
            check: count_3 { if (fiftyfifty) return; } count_4;
            count_1: { ++counts[1]; };
            count_2: { ++counts[2]; };
            count_3: { ++counts[3]; };
            count_4: { ++counts[4]; };
         endsequence
      end
      `checkd(counts[1], COUNT * 1 / 1);
      `checkd(counts[2], COUNT * 1 / 1);  // return
      `checkd(counts[3], COUNT * 1 / 1);
      `checkd(counts[4], COUNT * 1 / 2);  // break or return

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
