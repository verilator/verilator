// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

  class any_monitor #(
      type REQ = int,
      RSP = REQ
  );

    REQ req;
    RSP rsp;

    task run_phase();
      fork
        forever begin
          @req;
        end
        forever begin
          @rsp;
        end
      join_none
    endtask

  endclass

  typedef int q_t[$];

  any_monitor #(q_t, q_t) imon;

  initial $stop;

endmodule
