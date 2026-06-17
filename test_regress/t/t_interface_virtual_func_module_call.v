// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

interface iface;
  int cnt = 0;
  function void bump();
    cnt++;
  endfunction
endinterface

module t;
  iface theIf ();
  virtual iface vif;
  initial begin
    vif = theIf;
    vif.bump();
    if (theIf.cnt !== 1) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
