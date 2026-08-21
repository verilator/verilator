// DESCRIPTION: Verilator: Verilog Test module
//
// A procedural force or release of an externally forceable unpacked array,
// whole or by element, is visible through the array's read path.  The read
// path merges the procedural force's slots before overlaying the external
// per-element enable and value, and the per-element enable is left to the
// external interface rather than driven with the whole-value mask arithmetic
// that only a packed signal admits.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 BRDR LIFE
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0)
// verilog_format: on

module t;
  logic [7:0] arr[0:3] /* verilator forceable */;
  logic [7:0] src[0:3];

  initial begin
    for (int i = 0; i < 4; ++i) begin
      arr[i] = 8'h10 + 8'(i);
      src[i] = 8'ha0 + 8'(i);
    end
    #1;
    // Procedural force of one element is visible through the forceable read path
    force arr[1] = 8'hc1;
    #1;
    `checkh(arr[1], 8'hc1);
    `checkh(arr[0], 8'h10);
    // A live change of a sibling is unaffected
    arr[2] = 8'h77;
    #1;
    `checkh(arr[2], 8'h77);
    `checkh(arr[1], 8'hc1);
    release arr[1];
    #1;
    `checkh(arr[1], 8'hc1);

    // Procedural force of the whole forceable array compiles and takes effect
    force arr = src;
    #1;
    `checkh(arr[0], 8'ha0);
    `checkh(arr[3], 8'ha3);
    release arr;
    #1;
    `checkh(arr[0], 8'ha0);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
