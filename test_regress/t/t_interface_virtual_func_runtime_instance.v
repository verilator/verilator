// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

interface iface;
  bit x;

  function bit get_and_toggle();
    return x++;
  endfunction
endinterface

class Driver;
  virtual iface vif;

  function bit call();
    return vif.get_and_toggle();
  endfunction
endclass

module t;
  iface a ();
  iface b ();

  initial begin
    automatic Driver d = new;
    a.x = 1'b0;
    b.x = 1'b1;
    d.vif = a;
    if (d.call() !== 1'b0) $stop;
    d.vif = b;
    if (d.call() !== 1'b1) $stop;
    if (a.x !== 1'b1) $stop;
    if (b.x !== 1'b0) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
