// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

class PhaseNode;
   int m_successors[int];
   static mailbox #(PhaseNode) m_phase_hopper = new();
   static task run_phases();
      int succ;
      void'(m_phase_hopper.try_put(this));
      foreach (m_successors[succ])
         void'(m_phase_hopper.try_put(null));
   endtask
endclass
