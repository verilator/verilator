// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,
               expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%p exp='h%p\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)

module t (  /*AUTOARG*/
    // Inputs
    clk
);

  input clk;

  typedef struct {
    int fails;
    int passs;
  } result_t;

  result_t results[int];
  result_t expected[int];

  localparam MAX = 15;
  integer cyc = 1;

  assert property (@(posedge clk) 0 until 1)
    results[1].passs++;
  else results[1].fails++;

  assert property (@(posedge clk) 1 until 0)
    results[2].passs++;
  else results[2].fails++;

  assert property (@(posedge clk) cyc < 5 until cyc >= 5)
    results[3].passs++;
  else results[3].fails++;

  assert property (@(posedge clk) cyc % 3 == 0 until cyc % 5 == 0)
    results[4].passs++;
  else results[4].fails++;

  assert property (@(posedge clk) cyc % 3 != 0 until_with cyc % 4 != 0)
    results[5].passs++;
  else results[5].fails++;

  assert property (@(posedge clk) 0 s_until 1)
    results[6].passs++;
  else results[6].fails++;

  assert property (@(posedge clk) cyc < 5 s_until cyc >= 5)
    results[7].passs++;
  else results[7].fails++;

  assert property (@(posedge clk) cyc % 3 == 0 s_until cyc % 5 == 0)
    results[8].passs++;
  else results[8].fails++;

  // Check that s_until accepts immediately when RHS is true, even if LHS is false.
  assert property (@(posedge clk) cyc % 2 == 0 s_until 1)
    results[9].passs++;
  else results[9].fails++;

  // Check that s_until_with requires LHS when RHS is true on the same tick.
  assert property (@(posedge clk) 0 s_until_with 1)
    results[10].passs++;
  else results[10].fails++;

  assert property (@(posedge clk) 1 s_until_with cyc >= 5)
    results[11].passs++;
  else results[11].fails++;

  assert property (@(posedge clk) cyc <= 5 s_until_with cyc >= 5)
    results[12].passs++;
  else results[12].fails++;

  assert property (@(posedge clk) cyc < 5 s_until_with cyc >= 5)
    results[13].passs++;
  else results[13].fails++;

  always @(edge clk) begin
    ++cyc;
    if (cyc == MAX) begin
      expected[1] = '{0, 7};
      // expected[2] shouldn't be initialized
      expected[3] = '{0, 7};
      expected[4] = '{5, 2};
      expected[5] = '{2, 5};
      expected[6] = '{0, 7};
      expected[7] = '{0, 7};
      expected[8] = '{5, 2};
      expected[9] = '{0, 7};
      expected[10] = '{7, 0};
      expected[11] = '{0, 7};
      expected[12] = '{4, 3};
      expected[13] = '{7, 0};
      `checkh(results, expected);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
