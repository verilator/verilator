// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;

  int a1[$] = '{12, 13};
  int a2[$] = {14, 15};
  int a3[$] = '{16};
  int a4[$] = {17};

  int src[3], dest1[], dest2[];

  initial begin
    `checkd(a1.size, 2);
    `checkd(a1[0], 12);
    `checkd(a1[1], 13);

    `checkd(a2.size, 2);
    `checkd(a2[0], 14);
    `checkd(a2[1], 15);

    `checkd(a3.size, 1);
    `checkd(a3[0], 16);

    `checkd(a4.size, 1);
    `checkd(a4[0], 17);

    src = '{2, 3, 4};
    dest1 = new[2] (src);
    `checkd(dest1.size, 2);  // {2, 3}
    `checkd(dest1[0], 2);
    `checkd(dest1[1], 3);
    dest2 = new[4] (src);
    `checkd(dest2.size, 4);  // {2, 3, 4, 0}.
    `checkd(dest2[0], 2);
    `checkd(dest2[1], 3);
    `checkd(dest2[2], 4);
    `checkd(dest2[3], 0);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
