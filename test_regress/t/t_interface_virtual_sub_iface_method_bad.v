// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

interface inner_if;
  logic active = 1'b0;
  function automatic void set_active();
    active = 1'b1;
  endfunction
endinterface

interface outer_if;
  inner_if sub_if ();
endinterface

class cfg_c;
  virtual outer_if vif;
  function void doit();
    vif.sub_if.set_active();
  endfunction
endclass

module t;
  outer_if oif ();
  cfg_c cfg;
  initial begin
    cfg = new();
    cfg.vif = oif;
    cfg.doit();
  end
endmodule
