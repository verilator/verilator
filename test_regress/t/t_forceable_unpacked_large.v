// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Checks that a whole-array self-force ("force mem = mem;") on a large
// unpacked array compiles quickly rather than taking O(elements^2).

`define stop $stop
`define checkh(g,e) do if ((g) !== (e)) begin $write("%%Error: %s:%0d: got=%x exp=%x\n", `__FILE__,`__LINE__, (g),(e)); `stop; end while(0)

module t;
  localparam int ArraySize = 1024;
  localparam int MatSize = 64;

  logic [7:0] mem[0:ArraySize-1]  /*verilator forceable*/;
  logic [7:0] mat[0:MatSize-1][0:MatSize-1]  /*verilator forceable*/;
  logic go;
  logic go2;

  initial begin
    go = 1'b0;
    go2 = 1'b0;
    for (int i = 0; i < ArraySize; ++i) mem[i] = 8'h00;
    for (int i = 0; i < MatSize; ++i)
      for (int j = 0; j < MatSize; ++j) mat[i][j] = 8'h00;
  end

  // The idiom under test: a self-referential whole-array force.
  always @(posedge go) force mem = mem;
  always @(posedge go2) force mat = mat;

  initial begin
    #1;
    for (int i = 0; i < ArraySize; ++i) mem[i] = 8'(i);
    for (int i = 0; i < MatSize; ++i)
      for (int j = 0; j < MatSize; ++j) mat[i][j] = 8'(i * MatSize + j);
    #1;
    `checkh(mem[0], 8'd0);
    `checkh(mem[1], 8'd1);
    `checkh(mem[255], 8'd255);
    `checkh(mem[ArraySize-1], 8'(ArraySize - 1));
    `checkh(mat[0][0], 8'd0);
    `checkh(mat[0][1], 8'd1);
    `checkh(mat[MatSize-1][MatSize-1], 8'(MatSize * MatSize - 1));

    go = 1'b1;
    go2 = 1'b1;
    #1;
    for (int i = 0; i < ArraySize; ++i) mem[i] = 8'(255 - i);
    for (int i = 0; i < MatSize; ++i)
      for (int j = 0; j < MatSize; ++j) mat[i][j] = 8'(255 - (i * MatSize + j));
    #1;
    `checkh(mem[0], 8'd255);
    `checkh(mem[1], 8'd254);
    `checkh(mem[255], 8'd0);
    `checkh(mem[ArraySize-1], 8'(255 - (ArraySize - 1)));
    `checkh(mat[0][0], 8'd255);
    `checkh(mat[0][1], 8'd254);
    `checkh(mat[MatSize-1][MatSize-1], 8'(255 - (MatSize * MatSize - 1)));

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
