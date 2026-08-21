// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

interface CoverageIf;
  logic value;
endinterface

module t;
  covergroup cg(input virtual CoverageIf vif);
    cp: coverpoint 0;
  endgroup

  cg cov = new(null);

  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
