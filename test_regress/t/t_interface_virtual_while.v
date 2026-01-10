// DESCRIPTION: Verilator: Verilog Test module for SystemVerilog 'alias'
//
// Alias type check error test.
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

interface Bus;
  bit data;
endinterface

module t;
  Bus intf ();
  virtual Bus vif = intf;
  bit ok = 0;

  function logic write_data(output bit data);
    data = ~data;
    return data;
  endfunction

  initial @(posedge vif.data) ok = 1;

  initial begin
    #1;
    while (!write_data(vif.data)) $stop;
    #1 if (ok != 1) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
