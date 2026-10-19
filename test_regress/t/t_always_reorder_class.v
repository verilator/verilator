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
//
// Likewise, a variable selected through a handle carries no AstVarRef of it,
// and the variables an intra-assignment timing control reads are read when the
// NBA executes, so these accesses must stay in order too.

interface ifc;
  logic [15:0] w;
endinterface

module t;

  logic clk = 0;
  always #5 clk = ~clk;

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
      v = 2'd0;
      r0 = rd.getv();
      v = 2'd1;
      r1 = rd.getv();
      v = 2'd2;
      r2 = rd.getv();
      v = 2'd3;
      r3 = rd.getv();
    end
    else if (cyc == 2) begin
      $write("r0=%0d r1=%0d r2=%0d r3=%0d\n", r0, r1, r2, r3);
    end
  end

  logic [15:0] m_din = 16'h0;

  // An NBA waiting for the toggle after the one before it must not move before the toggle,
  // even to avoid a shadow variable of t_v. The locally-set t_go keeps the block from splitting.
  int t_go;
  logic t_ev = 1'b0;
  logic [15:0] t_v = 16'h0, t_q = 16'h0;
  always @(posedge clk) begin
    t_go = cyc;
    if (t_go > 2) begin
      if (t_go > 1) begin
        t_ev = ~t_ev;
        t_v <= m_din;
      end
      if (cyc == 4) t_q <= @(t_ev) t_v;
    end
  end

  // Writes to a variable directly and through a handle must stay in order
  ifc h_if ();
  virtual ifc h_vif = h_if;
  logic [15:0] h_q;
  always @(posedge clk) begin
    h_if.w = m_din;
    h_vif.w = ~m_din;
    h_q <= h_vif.w;
  end

  always @(posedge clk) begin
    m_din <= m_din + 16'h1111;
    if (cyc == 5 || cyc == 6) $write("t_q=%x h_q=%x\n", t_q, h_q);
    if (cyc == 6) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
