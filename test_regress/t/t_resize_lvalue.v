// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Alex Solomatnikov.
// SPDX-License-Identifier: CC0-1.0

package x_pkg;
  typedef bit unsigned [64-1:0] x_reg_data_t;
  virtual class x_reg;
    extern virtual task read(output int status, output x_reg_data_t value, input int path);
  endclass
  task x_reg::read(output int status, output x_reg_data_t value, input int path);
  endtask
endpackage

package s_c_env_pkg;
  import x_pkg::*;

  class r_reg_p_s_reg_n_doorbell extends x_reg;
    x_reg_data_t val;
    function new(int _val);
      val = _val;
    endfunction
    extern virtual task read(output int status, output x_reg_data_t value, input int path);
  endclass
  task r_reg_p_s_reg_n_doorbell::read(output int status, output x_reg_data_t value, input int path);
    status = 1;
    value = val;
  endtask

  class r_block_p_s_reg;
    rand r_reg_p_s_reg_n_doorbell n_doorbell;

    function new(int _val);
      n_doorbell = new(_val);
    endfunction
  endclass

  class r_top_s_reg;
    rand r_block_p_s_reg p_s[16];
  endclass

  class s_c_env;
    r_top_s_reg r_reg_model;
  endclass
endpackage

package s_c_sequences_pkg;
  import x_pkg::*;
  import s_c_env_pkg::*;
  class s_c_v_regs_seq;
    s_c_env m_env;
    virtual task body();
      int unsigned p, rdata;
      int status;
      if (m_env == null) m_env = new;
      if (m_env.r_reg_model == null) m_env.r_reg_model = new;
      foreach (m_env.r_reg_model.p_s[p]) begin
        if (m_env.r_reg_model.p_s[p] == null) begin
          m_env.r_reg_model.p_s[p] = new(p);
        end
        m_env.r_reg_model.p_s[p].n_doorbell.read(status, rdata, 0);
        if (status != 1) $stop;
        if (rdata != p) $stop;
      end
    endtask
  endclass
endpackage

module t;

  s_c_sequences_pkg::s_c_v_regs_seq seq;

  initial begin
    seq = new;
    seq.body();

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
