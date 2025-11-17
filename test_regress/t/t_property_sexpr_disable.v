// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2025 by Antmicro.
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

  result_t results [int];
  result_t expected[int];

  localparam MAX = 15;
  integer cyc = 0;

  assert property (@(posedge clk) disable iff (cyc == 4 || cyc > MAX) 1 ##1 cyc < 10)
    results[1].passs++;
  else results[1].fails++;

  assert property (@(posedge clk) disable iff (cyc == 5 || cyc > MAX) 1 ##1 cyc < 10)
    results[2].passs++;
  else results[2].fails++;

  always @(clk) begin
    ++cyc;
    if (cyc == MAX + 1) begin
       expected[1] = '{2, 2};
       expected[2] = '{2, 3};
      `checkh(results, expected);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
