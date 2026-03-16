// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class Packet;
  rand int unsigned m_length;
  rand byte m_data[];
  rand byte m_mask[];

  constraint c_length { m_length inside {[1:16]}; }
endclass

class MultiArray;
  rand int unsigned m_len_a;
  rand int unsigned m_len_b;
  rand int m_arr_a[];
  rand int m_arr_b[];

  constraint c_lens {
    m_len_a inside {[2:8]};
    m_len_b inside {[3:10]};
  }
endclass

module t;
  initial begin
    automatic Packet pkt = new;
    automatic MultiArray ma = new;
    automatic int ok;

    // Scenario 1: single class with two dynamic arrays sized by one field
    repeat (5) begin
      ok = pkt.randomize() with {
        m_data.size == m_length;
        m_mask.size == m_length;
        foreach (m_mask[i]) m_mask[i] inside {8'h00, 8'hFF};
      };
      `checkh(ok, 1)
      `checkh(pkt.m_data.size(), pkt.m_length)
      `checkh(pkt.m_mask.size(), pkt.m_length)
      // Verify mask values are constrained
      for (int i = 0; i < pkt.m_mask.size(); i++) begin
        if (pkt.m_mask[i] !== 8'h00 && pkt.m_mask[i] !== 8'hFF) begin
          $write("%%Error: m_mask[%0d]=%0h not in {00, FF}\n", i, pkt.m_mask[i]);
          `stop;
        end
      end
    end

    // Scenario 2: two arrays with independent size constraints
    repeat (5) begin
      ok = ma.randomize() with {
        m_arr_a.size == m_len_a;
        m_arr_b.size == m_len_b;
      };
      `checkh(ok, 1)
      `checkh(ma.m_arr_a.size(), ma.m_len_a)
      `checkh(ma.m_arr_b.size(), ma.m_len_b)
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
