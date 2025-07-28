// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

`define check_rand(cl, field, cond) \
begin \
   longint prev_result; \
   int ok = 0; \
   if (!bit'(cl.randomize())) $stop; \
   prev_result = longint'(field); \
   if (!(cond)) $stop; \
   repeat(9) begin \
      longint result; \
      if (!bit'(cl.randomize())) $stop; \
      result = longint'(field); \
      if (!(cond)) $stop; \
      if (result != prev_result) ok = 1; \
      prev_result = result; \
   end \
   if (ok != 1) $stop; \
end

class Rand1;
  rand bit [4:0] x;
  constraint c {$countones(x) == 1;}
endclass

class Rand2;
  rand bit [5:0] x;
  rand bit [2:0] y;
  constraint c {10'b1 + 10'($countones(x + 6'(y))) == 3;}
endclass

class Rand3;
  rand bit [32:0] x;
  constraint c {$countones(x) == 1;}
endclass

module t (  /*AUTOARG*/);
  Rand1 r1 = new;
  Rand2 r2 = new;
  Rand3 r3 = new;
  initial begin
    `check_rand(r1, r1.x, $countones(r1.x) == 1);
    `check_rand(r2, r2.x, 10'b1 + 10'($countones(r2.x + 6'(r2.y))) == 3);
    `check_rand(r3, r3.x, $countones(r3.x) == 1);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
