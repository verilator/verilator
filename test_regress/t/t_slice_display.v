// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Marco Frank
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

// Issue #5132: an array slice used as a bare value (not the LHS/RHS of an
// assignment) hit an internal error.
module t;
  byte mem[8] = '{1, 2, 3, 4, 5, 6, 7, 8};
  byte dmem[7:0] = '{10, 20, 30, 40, 50, 60, 70, 80};
  byte sub[4];

  // Ascending declaration with a non-zero low index
  byte emem[5:12] = '{201, 202, 203, 204, 205, 206, 207, 208};

  // Wide descending declaration with a non-zero low index
  logic [95:0] memwide[10:6] = '{96'hE444_4444_4444_4444_4444_4444, 96'hA000_0000_0000_0000_0000_0001,
                                  96'hB111_1111_1111_1111_1111_1111, 96'hC222_2222_2222_2222_2222_2222,
                                  96'hD333_3333_3333_3333_3333_3333};

  // For slicing the inner and outer dimensions of a 2D array
  byte mem2d[3][8] = '{'{1, 2, 3, 4, 5, 6, 7, 8}, '{11, 12, 13, 14, 15, 16, 17, 18},
                        '{21, 22, 23, 24, 25, 26, 27, 28}};

  task automatic check_arg(byte a[4]);
    `checkh(a[0], 8'd1);
    `checkh(a[3], 8'd4);
  endtask

  initial begin
    $display("%p", mem[0:3]);

    `checkh(mem[2:5][2], 8'd3);
    `checkh(mem[2:5][5], 8'd6);

    `checkh(dmem[5:2][5], 8'd30);
    `checkh(dmem[5:2][2], 8'd60);

    check_arg(mem[0:3]);

    `checkh(mem[0:3][2], 8'd3);

    sub = mem[0:3];
    `checkh(sub[0], 8'd1);
    `checkh(sub[3], 8'd4);

    // Indexing into a slice result uses the source array's index minus the
    // source array's own low bound (5 here), not the slice's own bounds.
    $display("%p", emem[7:10]);
    `checkh(emem[7:10][2], 8'd203);
    `checkh(emem[7:10][5], 8'd206);

    $display("%p", memwide[8:6]);

    $display("%p %p", mem[1:2], dmem[6:4]);

    $display("%p", mem2d[1][2:4]);
    `checkh(mem2d[1][2:4][2], 8'd13);
    `checkh(mem2d[1][2:4][4], 8'd15);

    // Slicing the outer dimension yields rows (each still an array), not elements
    $display("%p", mem2d[0:1]);
    `checkh(mem2d[0:1][0][0], 8'd1);
    `checkh(mem2d[0:1][1][3], 8'd14);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
