// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t;
  initial begin
    int q[$];

    // Basic slice assignment: overwrite middle elements
    q = '{10, 20, 30, 40, 50};
    q[1:3] = '{99, 88, 77};
    `checkh(q[0], 10);
    `checkh(q[1], 99);
    `checkh(q[2], 88);
    `checkh(q[3], 77);
    `checkh(q[4], 50);
    `checkh(q.size, 5);

    // Slice assignment at start
    q = '{10, 20, 30, 40, 50};
    q[0:1] = '{11, 22};
    `checkh(q[0], 11);
    `checkh(q[1], 22);
    `checkh(q[2], 30);
    `checkh(q[3], 40);
    `checkh(q[4], 50);

    // Slice assignment at end
    q = '{10, 20, 30, 40, 50};
    q[3:4] = '{44, 55};
    `checkh(q[0], 10);
    `checkh(q[1], 20);
    `checkh(q[2], 30);
    `checkh(q[3], 44);
    `checkh(q[4], 55);

    // Single-element slice
    q = '{10, 20, 30, 40, 50};
    q[2:2] = '{66};
    `checkh(q[0], 10);
    `checkh(q[1], 20);
    `checkh(q[2], 66);
    `checkh(q[3], 40);
    `checkh(q[4], 50);

    // Verify size unchanged after all operations
    `checkh(q.size, 5);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
