// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Class-handle covergroup constructor arguments are rebound to persistent
// covergroup members.  Virtual-interface arguments are not rebound, so
// dereferencing one after construction is unsupported and the covergroup must
// be ignored with COVERIGN.

interface CoverageInterface;
  bit test;
endinterface

class InterfaceArgumentMonitor;
  covergroup cov_interface(virtual CoverageInterface vif);
    cp: coverpoint vif.test;
  endgroup

  function new(virtual CoverageInterface vif);
    cov_interface = new(vif);
  endfunction
endclass

module t;
  CoverageInterface coverage_interface();
  InterfaceArgumentMonitor mon;

  initial begin
    mon = new(coverage_interface);
  end
endmodule
