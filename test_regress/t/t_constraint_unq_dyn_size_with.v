// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Francesco Urbani
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// A class whose dynamic arrays are sized by a class-level constraint (not
// one written inline in the randomize() with {} call below), combined with
// a randomize() with {} block that adds a whole-array unique{} constraint
// on one of those arrays and relies on a class-level foreach range
// constraint on the other. Both constraints must be checked against the
// arrays' solved (post-resize) length, not their pre-solve (empty) length.
//
// m_count spans a range (not a single fixed value), so repeated calls can
// settle on different sizes; the test checks that at least two different
// sizes are actually observed, confirming randomize() isn't stuck always
// returning the same solution.
class Frame;
  rand int m_count;
  rand int m_slots[];
  rand int m_vals[];

  constraint c_count {m_count inside {[2 : 5]};}
  constraint c_size {
    m_slots.size() == m_count;
    m_vals.size() == m_count;
  }
  constraint c_vals {
    foreach (m_vals[i])
    m_vals[i] inside {[0 : 9]};
  }
endclass

module t;
  initial begin
    automatic Frame fr = new;
    automatic int ok;
    automatic int first_count = -1;
    automatic bit found_variety = 0;
    repeat (50) begin
      ok = fr.randomize() with {unique {m_slots};};
      `checkd(ok, 1)
      `checkd(fr.m_slots.size(), fr.m_count)
      `checkd(fr.m_vals.size(), fr.m_count)
      if (first_count == -1) first_count = fr.m_count;
      else if (fr.m_count != first_count) found_variety = 1;
      for (int i = 0; i < fr.m_count; i++) begin
        if (fr.m_vals[i] < 0 || fr.m_vals[i] > 9) begin
          $write("%%Error: m_vals[%0d]=%0d not in [0:9]\n", i, fr.m_vals[i]);
          `stop;
        end
        for (int j = i + 1; j < fr.m_count; j++) begin
          if (fr.m_slots[i] == fr.m_slots[j]) begin
            $write("%%Error: m_slots[%0d] == m_slots[%0d] == %0d, not unique\n", i, j,
                   fr.m_slots[i]);
            `stop;
          end
        end
      end
    end
    if (!found_variety) begin
      $write("%%Error: randomize() always produced m_count=%0d, no variety across repeats\n",
             first_count);
      `stop;
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
