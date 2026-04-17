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

  always @(edge clk) begin
    ++cyc;
    if (cyc == MAX) begin
      expected[1] = '{0, 7};
      // expected[2] shouldn't be initialized
      expected[3] = '{0, 7};
      expected[4] = '{5, 2};
      expected[5] = '{2, 5};
      `checkh(results, expected);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
