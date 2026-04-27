// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

interface iface;
  function bit get();
    static bit x;
    return x++;
  endfunction
endinterface

class Holder;
  virtual iface vif;
endclass

module t;
  iface i();

  initial begin
    automatic Holder h = new;
    if (i.get() !== 1'b0) $stop;
    if (i.get() !== 1'b1) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
