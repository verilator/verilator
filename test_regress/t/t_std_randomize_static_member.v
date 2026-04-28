// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// Regression test for GitHub issue #7498:
// std::randomize() constraint referencing a static class member of a
// *different* class (accessed via a foreach loop) caused an internal error
// in V3Randomize ("Invalid reference?").

package tlogy_m_pkg;
  class v_cfg;
    static int num_of_ds = 0;
  endclass

  class tlogy_m;
    v_cfg v[$];
  endclass
endpackage

package s_pkg;
  import tlogy_m_pkg::*;
  class s_cfg;
    tlogy_m t_m;
    bit t_mode;
    int a_d_idx;

    function void setup_h_iw_cfg();
      if (t_mode) begin
        foreach (t_m.v[i]) begin
          if (std::randomize(
                  a_d_idx
              ) with {
                if (t_m.v[i].num_of_ds > 1) {
                  a_d_idx inside {[0 : (t_m.v[i].num_of_ds - 1)]};
                  a_d_idx != 0;
                }
              } == 0)
            $stop;
        end
      end
    endfunction
  endclass
endpackage

module t;
  import tlogy_m_pkg::*;
  import s_pkg::*;

  initial begin
    automatic s_cfg cfg = new;
    automatic tlogy_m tm = new;
    automatic v_cfg vc0 = new;
    automatic v_cfg vc1 = new;

    // Set up: push two entries in the queue and set num_of_ds = 3
    // so the constraint branch (num_of_ds > 1) is exercised.
    tm.v.push_back(vc0);
    tm.v.push_back(vc1);
    v_cfg::num_of_ds = 3;

    cfg.t_m = tm;
    cfg.t_mode = 1'b1;

    repeat (20) begin
      cfg.setup_h_iw_cfg();
      // When num_of_ds = 3 the constraint is:
      //   a_d_idx inside {[0:2]} && a_d_idx != 0
      // so a_d_idx must be 1 or 2.
      if (cfg.a_d_idx < 1 || cfg.a_d_idx > 2) $stop;
    end

    // Also verify that the "no constraint" branch (num_of_ds <= 1)
    // compiles and runs without crashing.
    v_cfg::num_of_ds = 0;
    cfg.setup_h_iw_cfg();

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
