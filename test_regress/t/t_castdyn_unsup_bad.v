// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

interface Iface;
  logic value;
  modport monitor(input value);
endinterface

module t;

  string q[$];
  int aarray[string];
  Iface intf();
  Iface ifaces[2] ();
  virtual Iface.monitor monitored;
  virtual Iface vifaces[2];

  initial begin
    $cast(q, aarray);
    $cast(monitored, intf);
    $cast(vifaces, ifaces);
  end

endmodule
