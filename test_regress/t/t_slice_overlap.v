// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// An assignment is evaluated in full before any of it is assigned, so an
// unpacked array assignment whose right-hand side reads the array it writes
// must see the old values throughout.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;

  int v [1:3];
  int w [0:3];
  int u [3:0];
  int two [0:1];
  int dyn [][1:3];
  int q [$][1:3];
  int as [string][1:3];
  int nest [1:2][1:3];

  initial begin
    // Reverse. Each element read must be the value before the assignment.
    v = '{1, 5, 2};
    v = '{v[3], v[2], v[1]};
    `checkd(v[1], 2);
    `checkd(v[2], 5);
    `checkd(v[3], 1);

    // Swap, which no ordering of element assignments alone can do
    two = '{7, 9};
    two = '{two[1], two[0]};
    `checkd(two[0], 9);
    `checkd(two[1], 7);

    // Rotate through an assignment pattern
    w = '{10, 20, 30, 40};
    w = '{w[3], w[0], w[1], w[2]};
    `checkd(w[0], 40);
    `checkd(w[1], 10);
    `checkd(w[2], 20);
    `checkd(w[3], 30);

    // Overlapping slice assignment, shifting up
    w = '{10, 20, 30, 40};
    w[1:3] = w[0:2];
    `checkd(w[0], 10);
    `checkd(w[1], 10);
    `checkd(w[2], 20);
    `checkd(w[3], 30);

    // Overlapping slice assignment, shifting down
    w = '{10, 20, 30, 40};
    w[0:2] = w[1:3];
    `checkd(w[0], 20);
    `checkd(w[1], 30);
    `checkd(w[2], 40);
    `checkd(w[3], 40);

    // A descending range behaves the same way
    u = '{1, 2, 3, 4};
    u = '{u[0], u[1], u[2], u[3]};
    `checkd(u[3], 4);
    `checkd(u[2], 3);
    `checkd(u[1], 2);
    `checkd(u[0], 1);

    // An element of a dynamic array, reached through a method rather than a
    // select, must behave the same way
    dyn = new[2];
    dyn[0] = '{1, 5, 2};
    dyn[0] = '{dyn[0][3], dyn[0][2], dyn[0][1]};
    `checkd(dyn[0][1], 2);
    `checkd(dyn[0][2], 5);
    `checkd(dyn[0][3], 1);

    // An element of a queue. Writing an element of a queue or associative array
    // warns SIDEEFFECT whatever the right-hand side is, as it re-evaluates the lookup.
    // verilator lint_off SIDEEFFECT
    q.push_back('{1, 5, 2});
    q[0] = '{q[0][3], q[0][2], q[0][1]};
    `checkd(q[0][1], 2);
    `checkd(q[0][2], 5);
    `checkd(q[0][3], 1);

    // An element of an associative array
    as["a"] = '{1, 5, 2};
    as["a"] = '{as["a"][3], as["a"][2], as["a"][1]};
    `checkd(as["a"][1], 2);
    `checkd(as["a"][2], 5);
    `checkd(as["a"][3], 1);
    // verilator lint_on SIDEEFFECT

    // An element of an array which itself contains an array, so the
    // temporary must take the type of the subarray, not of the whole
    nest[1] = '{1, 5, 2};
    nest[2] = '{3, 6, 4};
    nest[1] = '{nest[1][3], nest[1][2], nest[1][1]};
    `checkd(nest[1][1], 2);
    `checkd(nest[1][2], 5);
    `checkd(nest[1][3], 1);
    `checkd(nest[2][1], 3);
    `checkd(nest[2][2], 6);
    `checkd(nest[2][3], 4);

    // Swapping whole subarrays takes the type of the whole
    nest = '{nest[2], nest[1]};
    `checkd(nest[1][1], 3);
    `checkd(nest[1][2], 6);
    `checkd(nest[1][3], 4);
    `checkd(nest[2][1], 2);
    `checkd(nest[2][2], 5);
    `checkd(nest[2][3], 1);

    // No overlap: the ordinary case must be unaffected
    v = '{1, 2, 3};
    w = '{v[1], v[2], v[3], 0};
    `checkd(w[0], 1);
    `checkd(w[1], 2);
    `checkd(w[2], 3);
    `checkd(w[3], 0);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
