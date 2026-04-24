// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Output class type-parameter upcast through a 3-level extends chain.

package x_pkg;
  virtual class x_t_fifo_base #(type T = int);
    T m_val;
    virtual task put(input T t);
      m_val = t;
    endtask
    virtual task get(output T t);
      t = m_val;
    endtask
  endclass
  class x_t_fifo #(type T = int) extends x_t_fifo_base #(T);
  endclass
  class x_t_analysis_fifo #(type T = int) extends x_t_fifo #(T);
  endclass
endpackage

package s_t_pkg;
  class s_txn_base;
    int id = 0;
  endclass
endpackage

package s_x_pkg;
  import s_t_pkg::*;
  class s_x_txn extends s_txn_base;
    int x_val = 0;
  endclass
endpackage

package s_core_env_pkg;
  import x_pkg::*;
  import s_t_pkg::*;
  import s_x_pkg::*;
  class s_p_scoreboard;
    x_t_analysis_fifo #(s_x_txn) x_r_fifo;
    s_txn_base observed;
    extern task process_r();
  endclass
  task s_p_scoreboard::process_r();
    s_txn_base txn1;
    x_r_fifo.get(txn1);
    observed = txn1;
  endtask
endpackage

import x_pkg::*;
import s_x_pkg::*;
import s_core_env_pkg::*;

module tb_top;
  s_p_scoreboard sb;
  s_x_txn tx;
  initial begin
    sb = new;
    sb.x_r_fifo = new;
    tx = new;
    tx.id = 77;
    tx.x_val = 99;
    sb.x_r_fifo.put(tx);
    sb.process_r();
    if (sb.observed === null) $stop;
    if (sb.observed.id !== 77) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
