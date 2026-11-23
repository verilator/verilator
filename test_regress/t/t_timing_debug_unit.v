// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// In the compilation-unit package
event unit_ev;

class UCls;
  static event ev;
endclass

package \pkg.esc ;
  event ev;
endpackage

module sub;
  event ev;
endmodule

module t;
  // User identifiers with the name of the compilation-unit package
  logic \$unit = 1'b0;
  if (1) begin : g
    sub \$unit ();
  end

  initial begin
    fork
      @(unit_ev);
      @(UCls::ev);
      @(\pkg.esc ::ev);
      @(posedge \$unit );
      @(g.\$unit .ev);
    join
    $write("*-* All Finished *-*\n");
    $finish;
  end

  initial begin
    #1->unit_ev;
    #1->UCls::ev;
    #1->\pkg.esc ::ev;
    #1 \$unit = 1'b1;
    #1->g.\$unit .ev;
  end
endmodule
