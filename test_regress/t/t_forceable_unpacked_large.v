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

  logic [7:0] mem[0:ArraySize-1]  /*verilator forceable*/;
  logic go;

  initial begin
    go = 1'b0;
    for (int i = 0; i < ArraySize; ++i) mem[i] = 8'h00;
  end

  // The idiom under test: a self-referential whole-array force.
  always @(posedge go) force mem = mem;

  initial begin
    #1;
    for (int i = 0; i < ArraySize; ++i) mem[i] = 8'(i);
    #1;
    `checkh(mem[0], 8'd0);
    `checkh(mem[1], 8'd1);
    `checkh(mem[255], 8'd255);
    `checkh(mem[ArraySize-1], 8'(ArraySize - 1));

    go = 1'b1;
    #1;
    for (int i = 0; i < ArraySize; ++i) mem[i] = 8'(255 - i);
    #1;
    `checkh(mem[0], 8'd255);
    `checkh(mem[1], 8'd254);
    `checkh(mem[255], 8'd0);
    `checkh(mem[ArraySize-1], 8'(255 - (ArraySize - 1)));

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
