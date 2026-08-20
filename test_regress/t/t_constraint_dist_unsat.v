// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 BRDR LIFE
// SPDX-License-Identifier: CC0-1.0

// A genuinely unsatisfiable 'dist' still reports, and a merely inconvenient one
// does not.
//
// Discarding a conflicting weight draw and failing the solve look alike from
// inside the solver -- both come back unsat -- so the two must stay
// distinguishable.  A hard dist whose set is emptied by another constraint has
// no solution and has to be reported; a hard dist whose set is only narrowed
// must solve silently.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// No value satisfies both: the dist set and the hard constraint are disjoint
class Impossible;
  rand bit [7:0] x;
  constraint c_dist { x dist {8'd1 := 1, 8'd2 := 1}; }
  constraint c_hard { x == 8'd5; }
endclass

// Satisfiable: the hard constraint only excludes part of the set
class Narrowed;
  rand bit [7:0] y;
  constraint c_dist { y dist {8'd1 := 1, 8'd2 := 1}; }
  constraint c_hard { y == 8'd2; }
endclass

module t;
  initial begin
    Impossible o1;
    Narrowed o2;
    o1 = new;
    o2 = new;

    `checkd(o1.randomize(), 0)

    repeat (20) begin
      `checkd(o2.randomize(), 1)
      `checkd(o2.y, 8'd2)
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
