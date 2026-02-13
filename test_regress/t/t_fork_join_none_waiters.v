// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

class events_holder;
  event ev;
endclass

module test;
  events_holder m_events[int];
  int waiters_done = 0;

  initial begin
    m_events[0] = new;
    fork
      begin
        @(m_events[0].ev);
        waiters_done++;
      end
      begin
        @(m_events[0].ev);
        waiters_done++;
      end
    join_none
    #1;
    ->m_events[0].ev;

    #1;
    if (waiters_done == 2) $finish;
  end

  initial #10000ns $stop;
endmodule
