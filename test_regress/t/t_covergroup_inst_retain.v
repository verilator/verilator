// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Retirement under --coverage: the node is kept, but stops counting as live.
//
// Under --coverage, registerBins() has given the coverage database raw pointers
// into each instance's bin counts, read at write() time, so the free path is off
// and a retired instance is only marked dead.
//
// t_covergroup_inst_lifetime pins the reported half of that contract (a dead
// instance's counts still appear).  This pins the other half: a retained node
// must not count as live.  Every other retirement test builds without
// --coverage, so an implementation that returned m_insts.size() would pass the
// rest of the suite.
//
// Handles are dropped and checked two clock edges later; garbage is deleted at
// the start of a later eval_step.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkalive(hv) do if ((hv) == null) begin $write("%%Error: %s:%0d:  handle is null\n", `__FILE__,`__LINE__); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  int cyc = 0;
  logic [1:0] v;

  covergroup cg_retain;
    cp: coverpoint v {
      bins b0 = {0};
      bins b1 = {1};
      bins b2 = {2};
      bins b3 = {3};
    }
  endgroup

  // Every handle below is read through `checkalive before being dropped: a
  // handle written and never read is localized and dies in its creating edge.
  cg_retain r1, r2;

  function int live();
    live = $c32(
        "Verilated::threadContextp()->covergroupRegistryp()->liveInstanceCount(\"cg_retain\")");
  endfunction
  function int created();
    created = $c32(
        "Verilated::threadContextp()->covergroupRegistryp()->createdInstanceCount(\"cg_retain\")");
  endfunction
  function int retired();
    retired = $c32(
        "Verilated::threadContextp()->covergroupRegistryp()->retiredInstanceCount(\"cg_retain\")");
  endfunction
  function int retired_cov_x100();
    retired_cov_x100 = $c32(
        "(int)(Verilated::threadContextp()->covergroupRegistryp()",
        "->retiredCoverage(\"cg_retain\") * 100.0 + 0.5)");
  endfunction

  // Hit bins lo .. hi.  Sampling from a loop, not straight-line assignments.
  task automatic sample_range(cg_retain cg, int lo, int hi);
    for (int i = lo; i <= hi; ++i) begin
      v = i[1:0];
      cg.sample();
    end
  endtask

  always @(posedge clk) begin
    cyc <= cyc + 1;
    case (cyc)
      0: begin
        r1 = new;
        sample_range(r1, 0, 1);  // 2 of 4 bins -> 50%
      end

      2: begin
        `checkd(live(), 1);
        `checkd(created(), 1);
        `checkd(retired(), 0);
        `checkalive(r1);
        r1 = null;
      end

      4: begin
        // The node is still there, but dead.  A liveInstanceCount() returning
        // m_insts.size() would read 1 here.
        `checkd(live(), 0);
        `checkd(created(), 1);
        `checkd(retired(), 1);
        `checkd(retired_cov_x100(), 5000);

        r2 = new;
        sample_range(r2, 2, 2);  // 1 of 4 bins -> 25%
      end

      6: begin
        // A live instance alongside a retained dead one: exactly one is live.
        `checkd(live(), 1);
        `checkd(created(), 2);
        `checkd(retired(), 1);
        `checkalive(r2);
        r2 = null;
      end

      8: begin
        `checkd(live(), 0);
        `checkd(created(), 2);
        `checkd(retired(), 2);
        `checkd(retired_cov_x100(), 3750);  // mean of 50% and 25%

        $write("*-* All Finished *-*\n");
        $finish;
      end

      default: ;
    endcase
  end
endmodule
