// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Verilator Authors.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Model a UVM-style factory that is declared before the class it constructs.
// Width analysis may reach the constructed class's embedded covergroup through
// this factory before visiting the synthetic covergroup class normally.
typedef class CoveredConfig;

class EarlyFactory;
  static function CoveredConfig create();
    CoveredConfig config_h = new;
    return config_h;
  endfunction
endclass

class CoveredConfig;
  covergroup config_cg;
    option.auto_bin_max = 1024;
  endgroup

  function new();
    config_cg = new;
  endfunction
endclass

module t;
  CoveredConfig config_h;

  initial begin
    config_h = EarlyFactory::create();
    if (config_h == null) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
