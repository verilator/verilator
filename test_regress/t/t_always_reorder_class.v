// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// V3Reorder builds its scoreboard from the AstVarRefs it can see at each
// statement.  A class method is not inlined, so a module-scope variable it
// reads carries no AstVarRef at the call site: the assignments to that variable
// and the calls that read it land in unrelated weakly-connected components and
// are free to be interleaved arbitrarily.  Each call below must observe the
// value assigned immediately before it, so the reads come back 0, 1, 2, 3.
//
// A covergroup's sample() is one of these methods, reading its coverpoint
// variables, but there is nothing covergroup-specific about the hazard.
// Note: The sampling block below is kept free of display tasks, as
// those are impure and would constrain the ordering on their own.

module t (
    input clk
);

  int cyc = 0;
  logic [1:0] v;
  int r0, r1, r2, r3;

  class Reader;
    function int getv();
      return int'(v);
    endfunction
  endclass

  Reader rd = new;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 1) begin
      v  = 2'd0;
      r0 = rd.getv();
      v  = 2'd1;
      r1 = rd.getv();
      v  = 2'd2;
      r2 = rd.getv();
      v  = 2'd3;
      r3 = rd.getv();
    end else if (cyc == 2) begin
      $write("r0=%0d r1=%0d r2=%0d r3=%0d\n", r0, r1, r2, r3);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
