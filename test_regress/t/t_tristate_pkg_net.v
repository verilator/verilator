// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

package pk;
  wire [6:0] w7;
  wire [3:0] w4;
endpackage

module t;
  wire [3:0] m4;

  initial begin
    // Undriven package nets are high impedance
    if (pk::w7 !== 7'bzzzzzzz) $stop;
    if (!(pk::w7 === 7'bzzzzzzz)) $stop;
    if (pk::w4[1:0] !== 2'bz) $stop;
    if ($countbits(pk::w4, 'z) != $countbits(m4, 'z)) $stop;
    if (pk::w4 ==? 4'bzzzz) begin
    end
    else begin
      $stop;
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
