// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Covergroup instance retirement: registry bookkeeping and the dead instance's
// residue when the last SV handle drops.
//
// t_covergroup_inst_churn proves nodes do not accumulate, but never holds more
// than one instance, so the retired slot is always both first and last and the
// erase-by-swap fixup is never exercised.  This test exercises it, and pins the
// residue values.
//
// Built WITHOUT --coverage, so retirement takes the free path;
// t_covergroup_inst_lifetime pins the retained side.  Handles are dropped and
// checked two clock edges later, since garbage is deleted in a later eval_step.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkr(gotv,expv) do if ((((gotv) - (expv)) > 0.001) || (((expv) - (gotv)) > 0.001)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkalive(hv) do if ((hv) == null) begin $write("%%Error: %s:%0d:  handle is null\n", `__FILE__,`__LINE__); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  int cyc = 0;
  logic [1:0] v;

  // Three covergroup types, so each scenario's residue is read in isolation:
  // the accessors are per-type, and one shared type would average the three
  // scenarios together and pin nothing.

  // Slot bookkeeping under erase-by-swap.  Several instances live at once.
  covergroup cg_slot;
    cp: coverpoint v {
      bins b0 = {0};
      bins b1 = {1};
      bins b2 = {2};
      bins b3 = {3};
    }
  endgroup

  // Residue value: one instance, partially covered, harvested on death.
  covergroup cg_fold;
    cp: coverpoint v {
      bins b0 = {0};
      bins b1 = {1};
      bins b2 = {2};
      bins b3 = {3};
    }
  endgroup

  // Residue of an instance that was never sampled.
  covergroup cg_none;
    cp: coverpoint v {
      bins b0 = {0};
      bins b1 = {1};
      bins b2 = {2};
      bins b3 = {3};
    }
  endgroup

  cg_slot a, b, c, d, e, f;
  cg_fold g;
  cg_none h;

  // Every handle below is read through `checkalive before being dropped: a
  // handle written and never read is localized and dies in its creating edge.

  // The registry accessors are C++-only on purpose: they are test and debug
  // observability, not an SV-visible surface, so they are reached through $c.
  // The type name is the covergroup's name as the code generator emits it.
  function int slot_live();
    slot_live = $c32(
        "Verilated::threadContextp()->covergroupRegistryp()->liveInstanceCount(\"cg_slot\")");
  endfunction
  function int slot_retired();
    slot_retired = $c32(
        "Verilated::threadContextp()->covergroupRegistryp()->retiredInstanceCount(\"cg_slot\")");
  endfunction
  // Coverage in hundredths of a percent, so the checks are integer-exact rather
  // than float comparisons smuggled through $c.
  function int slot_retired_cov_x100();
    slot_retired_cov_x100 = $c32(
        "(int)(Verilated::threadContextp()->covergroupRegistryp()",
        "->retiredCoverage(\"cg_slot\") * 100.0 + 0.5)");
  endfunction
  function int fold_retired();
    fold_retired = $c32(
        "Verilated::threadContextp()->covergroupRegistryp()->retiredInstanceCount(\"cg_fold\")");
  endfunction
  function int fold_retired_cov_x100();
    fold_retired_cov_x100 = $c32(
        "(int)(Verilated::threadContextp()->covergroupRegistryp()",
        "->retiredCoverage(\"cg_fold\") * 100.0 + 0.5)");
  endfunction
  function int none_retired();
    none_retired = $c32(
        "Verilated::threadContextp()->covergroupRegistryp()->retiredInstanceCount(\"cg_none\")");
  endfunction
  function int none_retired_cov_x100();
    none_retired_cov_x100 = $c32(
        "(int)(Verilated::threadContextp()->covergroupRegistryp()",
        "->retiredCoverage(\"cg_none\") * 100.0 + 0.5)");
  endfunction
  // retiredCoverage() reports "no data" as a negative, distinct from 0.0; the
  // x100 helpers cannot tell the two apart.
  function int slot_retired_cov_is_none();
    slot_retired_cov_is_none = $c32(
        "(Verilated::threadContextp()->covergroupRegistryp()",
        "->retiredCoverage(\"cg_slot\") < 0.0 ? 1 : 0)");
  endfunction

  // Queries against a type the registry has never heard of: 0 / 0 / 0 / negative.
  function int unknown_live();
    unknown_live = $c32(
        "Verilated::threadContextp()->covergroupRegistryp()",
        "->liveInstanceCount(\"cg_no_such_type\")");
  endfunction
  function int unknown_created();
    unknown_created = $c32(
        "Verilated::threadContextp()->covergroupRegistryp()",
        "->createdInstanceCount(\"cg_no_such_type\")");
  endfunction
  function int unknown_retired();
    unknown_retired = $c32(
        "Verilated::threadContextp()->covergroupRegistryp()",
        "->retiredInstanceCount(\"cg_no_such_type\")");
  endfunction
  function int unknown_cov_is_none();
    unknown_cov_is_none = $c32(
        "(Verilated::threadContextp()->covergroupRegistryp()",
        "->retiredCoverage(\"cg_no_such_type\") < 0.0 ? 1 : 0)");
  endfunction

  // Hit every bin of one cg_slot instance, so get_inst_coverage() reads 100%.
  task automatic sample_all(cg_slot cg);
    for (int i = 0; i < 4; ++i) begin
      v = i[1:0];
      cg.sample();
    end
  endtask

  // Hit 'nbins' of cg_fold's four bins.
  task automatic sample_fold(cg_fold cg, int nbins);
    for (int i = 0; i < nbins; ++i) begin
      v = i[1:0];
      cg.sample();
    end
  endtask

  always @(posedge clk) begin
    cyc <= cyc + 1;
    case (cyc)
      0: begin
        // Slots 0,1,2,3.
        a = new;
        b = new;
        c = new;
        d = new;

        // cg_fold: 2 of 4 bins -> 50%.  Sampled while live; the fold must read
        // these counts before the node is unlinked, not after.
        g = new;
        sample_fold(g, 2);

        // cg_none: created and never sampled.
        h = new;
      end

      2: begin
        `checkd(slot_live(), 4);
        `checkd(slot_retired(), 0);
        // Four instances exist but none has died, so the residue is empty and
        // must report "no data" rather than 0%.
        `checkd(slot_retired_cov_is_none(), 1);

        // A type name the registry has never seen.
        `checkd(unknown_live(), 0);
        `checkd(unknown_created(), 0);
        `checkd(unknown_retired(), 0);
        `checkd(unknown_cov_is_none(), 1);

        `checkalive(b);
        b = null;  // slot 1, not last -> d is swapped down into slot 1
        `checkalive(g);
        g = null;
        `checkalive(h);
        h = null;
      end

      4: begin
        `checkd(slot_live(), 3);
        `checkd(slot_retired(), 1);

        // The fold ran before the unlink, on live items.  A fold that ran after
        // the free reads destroyed vectors and reports garbage or 0, not 50%.
        `checkd(fold_retired(), 1);
        `checkd(fold_retired_cov_x100(), 5000);

        // A never-sampled instance counts as 0%, per IEEE 1800-2023 19.11.3.
        // Pinned here so a change is visible.
        `checkd(none_retired(), 1);
        `checkd(none_retired_cov_x100(), 0);

        e = new;  // slot 3
      end

      6: begin
        `checkd(slot_live(), 4);
        `checkd(slot_retired(), 1);
        // d now sits in slot 1.  Retiring it swaps e (slot 3) down into slot 1;
        // if e's slot is not rewritten, e is the node that gets erased next.
        `checkalive(d);
        d = null;
      end

      8: begin
        `checkd(slot_live(), 3);
        `checkd(slot_retired(), 2);

        // e must still be the node it was: intact, samplable, and its own.
        sample_all(e);
        `checkr(e.get_inst_coverage(), 100.0);

        f = new;  // slot 3 -- the entry a stale e.m_slot would point at
      end

      10: begin
        `checkd(slot_live(), 4);
        `checkd(slot_retired(), 2);
        // With the fixup this retires e (slot 1); without it, e's stale slot 3
        // retires f.  Counts match either way -- cycle 12 is what notices.
        `checkalive(e);
        e = null;
      end

      12: begin
        `checkd(slot_live(), 3);
        `checkd(slot_retired(), 3);

        // If f was erased instead of e, this reads freed storage (ASAN variant)
        // and e's node is orphaned in the registry, which cycle 14 sees as a
        // live count that never reaches 0.
        sample_all(f);
        `checkr(f.get_inst_coverage(), 100.0);

        `checkalive(a);
        a = null;
        `checkalive(c);
        c = null;
        `checkalive(f);
        f = null;
      end

      14: begin
        `checkd(slot_live(), 0);
        `checkd(slot_retired(), 6);
        // a, b, c, d never sampled (0%); e and f fully covered (100%).
        `checkd(slot_retired_cov_x100(), 3333);
        // ... and now it is real data, not the empty-residue sentinel.
        `checkd(slot_retired_cov_is_none(), 0);

        $write("*-* All Finished *-*\n");
        $finish;
      end

      default: ;
    endcase
  end
endmodule
