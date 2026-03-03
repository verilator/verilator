// DESCRIPTION: Verilator: Localparam with package function call using interface param
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

package pkg;
  function automatic bit fn(int value);
    return (value > 0) ? 1'b1 : 1'b0;
  endfunction
endpackage

interface ifc();
  localparam int PARAM = 1;
endinterface

module mod(ifc i);
  localparam bit lpbit = pkg::fn(i.PARAM);
endmodule

module t;
  ifc i();
  mod m(.i);

  initial begin
    // fn(1) returns 1'b1 since 1 > 0
    if (m.lpbit !== 1'b1) begin
      $display("%%Error: m.lpbit=%0b expected 1", m.lpbit);
      $stop;
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
