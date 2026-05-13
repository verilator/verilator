// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

interface intf;
  int status;
  function int get_status;
    return status;
  endfunction
endinterface

class cls;
  virtual intf i;
  function int get_status;
    return i.get_status;
  endfunction
endclass

module t;
  intf intf();
  cls c;
  initial begin
    intf.status = 'hdeadbeef;
    c = new();
    c.i = intf;
    if (c.get_status !== 'hdeadbeef) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
