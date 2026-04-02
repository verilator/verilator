// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

interface str_if;
  string s;
endinterface

module t;
  str_if sif();
  virtual str_if vif = sif;

  initial begin
    vif.s = "hello";
    $finish;
  end
endmodule
