// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class ClsNarrow #(parameter int WIDTH);
   randc bit [WIDTH-1:0] m_var;

   function void test;
      automatic int i;
      automatic int count[2**WIDTH];
      automatic int maxcount;
      automatic bit bad;
      automatic int randomize_result;
      $display("Test %m");
      for (int trial = 0; trial < 10; ++trial) begin
         for (i = 0; i < (2 ** WIDTH); ++i) begin
            randomize_result = randomize();
            if (randomize_result !== 1) $stop;
`ifdef TEST_VERBOSE
            $display("w%0d i=%0d m_var=%x", WIDTH, i, m_var);
`endif
            ++count[m_var];
         end
      end
      maxcount = count[0];
      bad = '0;
`ifndef TEST_IGNORE_RANDC
      for (i = 0; i < (2 ** WIDTH); ++i) begin
         if (maxcount != count[i]) bad = '1;
      end
`endif
      if (bad) begin
         $display("%%Error: count mismatch");
         for (i = 0; i < (2 ** WIDTH); ++i) begin
            $display("w%0d entry[%0d]=%0d", WIDTH, i, count[i]);
         end
         $stop;
      end
   endfunction

endclass

class ClsWide #(parameter int WIDTH);
   randc bit [WIDTH-1:0] m_var;

   function void test;
      automatic bit [WIDTH-1:0] last;
      automatic int randomize_result;
      $display("Test %m");
      for (int i = 0; i < 100; ++i) begin
         randomize_result = randomize();
         if (randomize_result !== 1) $stop;
`ifdef TEST_VERBOSE
         $display("ww%0d i=%0d m_var=%x", WIDTH, i, m_var);
`endif
         if (i != 0) begin
`ifndef TEST_IGNORE_RANDC
            if (m_var == last) $stop;
`endif
         end
         last = m_var;
      end
   endfunction

endclass

class ClsEnum;
   typedef enum bit [3:0] {
      TWO = 2,
      FIVE = 5,
      SIX = 6
   } enum_t;

   randc enum_t m_var;

   function void test;
      automatic enum_t last;
      automatic int randomize_result;
      $display("Test %m");
      for (int trial = 0; trial < 10; ++trial) begin
         for (int i = 0; i < 3; ++i) begin
            randomize_result = randomize();
            if (randomize_result !== 1) $stop;
`ifdef TEST_VERBOSE
            $display("we i=%0d m_var=%x", i, m_var);
`endif
            if (m_var != TWO && m_var != FIVE && m_var != SIX) $stop;
            if (i != 0) begin
`ifndef TEST_IGNORE_RANDC
               if (m_var == last) $stop;
`endif
            end
            last = m_var;
         end
      end
   endfunction

endclass

module t (/*AUTOARG*/);

   ClsNarrow #(1) c1;  // Degenerate case
   ClsNarrow #(2) c2;
   ClsNarrow #(3) c3;
   ClsNarrow #(3) c3b;  // Need to have two of same size to cover dtype dedup code
   ClsNarrow #(9) c9;
   ClsWide #(31) c31;
   ClsWide #(32) c32;
   ClsEnum ce;

   initial begin
      c1 = new;
      c1.test();
      c2 = new;
      c2.test();
      c3 = new;
      c3.test();
      c3b = new;
      c3b.test();
      c9 = new;
      c9.test();
      c31 = new;
      c31.test();
      c32 = new;
      c32.test();
      ce = new;
      ce.test();
      $write("*-* All Finished *-*\n");
      $finish();
   end

endmodule
