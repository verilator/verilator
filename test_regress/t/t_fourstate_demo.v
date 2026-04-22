// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

`define STRINGIFY(x) `"x`"

module t;
  bit clk = 1;
  wire x;
  tri y;
  wire t;
  triand u;
  wor z;
  wor z3;
  wor [3:0] z2;
  wire lost;
  wire open = 'z;
  assign x = clk;
  assign z = x;
  assign z = y;
  assign u = z;
  assign u = x;
  assign t = u;
  assign t = x;
  assign t = y;
  wire [128:0] xx;
  logic [128:0] xy;
  logic [128:0] xz;
  bit one = 1;
  always #5 clk <= ~clk;

  always #10 xz = ~xz;
  assign xx = xy;
  assign xx = xz;

  logic vvv;
  // logic example;
  task writeFourState(logic a);
    if (a === 1'b1) $write("1");
    else if (a === 1'b0) $write("0");
    else if (a === 1'bx) $write("x");
    else if (a === 1'bz) $write("z");
    else $stop;
  endtask
  task print(logic a, logic b);
    // $write(" %1d & %1d == %1d |", a, b, a & b);
    $write(" ");
    writeFourState(a);
    $write(" ^ ");
    writeFourState(b);
    $write(" == ");
    writeFourState(a ^ b);
    $write(" |");
  endtask
  initial begin
    static int n = 12;
    static integer res = 'b01xz | n;
    if ((int'('b01xz | n)) === n);
    else $stop;
    #1;
    xy = 442093479423423857275364882039482723489;
    xz = 442093479423423857275364882039482723489;
    $dumpfile(`STRINGIFY(`TEST_DUMPFILE));
    $dumpvars();
    $write("res: ");
    writeFourState(res[0]);
    $write("\n");
    $write("res: ");
    writeFourState(res[1]);
    $write("\n");
    $write("res: ");
    writeFourState(res[2]);
    $write("\n");
    $write("res: ");
    writeFourState(res[3]);
    $write("\n");
    $write("res: ");
    writeFourState(res[31]);
    $write("\n");
    $write("      ZERO       | ONE        | X          | Z      \n");
    $write("ZERO ");
    print(0, 0);
    print(0, 1);
    print(0, 'x);
    print(0, 'z);
    $write("\nONE  ");
    print(1, 0);
    print(1, 1);
    print(1, 'x);
    print(1, 'z);
    $write("\nX    ");
    print('x, 0);
    print('x, 1);
    print('x, 'x);
    print('x, 'z);
    $write("\nZ    ");
    print('z, 0);
    print('z, 1);
    print('z, 'x);
    print('z, 'z);
    $write("\n");
    $write("x wire: ");
    writeFourState(x);
    $write("\n");
    $write("z wor: ");
    writeFourState(z);
    $write("\n");
    $write("u triand: ");
    writeFourState(u);
    $write("\n");
    $write("t wire: ");
    writeFourState(t);
    $write("\n");
    #1;
    $write("x wire: ");
    writeFourState(x);
    $write("\n");
    $write("z wor: ");
    writeFourState(z);
    $write("\n");
    $write("u triand: ");
    writeFourState(u);
    $write("\n");
    $write("t wire: ");
    writeFourState(t);
    $write("\n");
    $write("vvv: ");
    writeFourState(vvv);
    $write("\n");
    if ('x & (t !== 0)) $stop;
    else if (t != 1) $stop;
    else if (~(t & one | t)) $stop;
    else if (t | one) $write("Bye\n");
    else $stop;
    #100;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
