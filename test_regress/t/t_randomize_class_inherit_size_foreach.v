// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Scenario A: minimized reproducer from issue #7558 reporter (2026-05-15).
// Dynamic array, parameterized virtual class wrapping the rand class,
// 3-level extends, randomize() reached indirectly via `req` field.
package uvm_pkg;
  virtual class uvm_sequence #(type REQ = int);
    REQ req;
  endclass
endpackage

package s_t_pkg;
  import uvm_pkg::*;
  parameter S_D_WIDTH = 64;

  class s_txn_base;
    rand logic [S_D_WIDTH-1:0] p_d[];
    rand int d_s_dw;
    constraint d_s_dw_c {
      p_d.size() == d_s_dw / 16;
      d_s_dw inside {[16 : 80]};
    }
  endclass

  class s_t_txn extends s_txn_base;
    constraint d_incremental {
      foreach (p_d[i]) if (i == 0) p_d[i] == '0;
    }
  endclass

  class t_base_sequence extends uvm_sequence#(s_t_txn);
  endclass

  class t_base_port_seq extends t_base_sequence;
  endclass

  class p_c_seq extends t_base_port_seq;
    virtual task body();
      void'(req.randomize());
    endtask
  endclass
endpackage

// Scenario B: same bug class but on a queue (rand int q[$]) -- exercises
// the queue dtype dispatch in V3Randomize, distinct from dynamic array.
package q_pkg;
  class q_base;
    rand int q[$];
    constraint c_size {q.size() == 3;}
  endclass

  class q_derived extends q_base;
    constraint c_inc {foreach (q[i]) q[i] == i * 10;}
  endclass
endpackage

module t;
  import s_t_pkg::*;
  import q_pkg::*;

  initial begin
    // Scenario A: solomatnikov reproducer
    static p_c_seq seq = new();
    seq.req = new();
    repeat (5) begin
      seq.body();
      `checkd(seq.req.p_d.size(), seq.req.d_s_dw / 16)
      if (seq.req.p_d.size() > 0) `checkd(seq.req.p_d[0], 0)
    end

    // Scenario B: queue extension
    begin
      automatic q_derived qd = new();
      repeat (5) begin
        `checkd(qd.randomize(), 1)
        `checkd(qd.q.size(), 3)
        foreach (qd.q[i]) `checkd(qd.q[i], i * 10)
      end
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
