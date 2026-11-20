// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module automatic t;
  task automatic at(input int ai);
    int av;
    static int as;
    av = ai;
    as = ai;
    $display("%0d", at.av);  // Illegal (IEEE 1800-2023 13.3.1), but not detected in its own task.
  endtask

  function automatic int af(input int fi);
    int fv;
    fv = fi;
    return fv;
  endfunction

  task static st(input int si);
    automatic int sav;
    int ssv;
    sav = si;
    ssv = si;
  endtask

  int w;
  assign w = at.av;

  initial begin
    at.av = 1;
    $display("%0d", at.av);
    $display("%0d", at.ai);
    $display("%0d", at.as);  // Static storage is legal.
    $display("%0d", af.fv);
    $display("%0d", af.fi);
    $display("%0d", af.af);
    $display("%0d", st.sav);
    $display("%0d", st.ssv);  // Static storage is legal.
    $display("%0d", st.si);  // Static formal argument is legal.
    $display("%0d", dt.dv);
    $display("%0d", df.fv);
  end

  task dt;
    int dv;
    dv = 1;
  endtask

  function int df;
    int fv;
    fv = 2;
    return fv;
  endfunction
endmodule
