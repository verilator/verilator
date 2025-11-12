// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module x;
  event a;
  int counter = 0;

  initial begin
    fork
      begin
        @a;
        ->a;
        @a;
        counter++;
      end
    join_none
    #1;
    ->a;
  end
  always begin
    @a;
    ->a;
    @a;
    counter++;
  end
  final begin
    if (counter != 1) $stop;
    $write("*-* All Finished *-*\n");
  end
endmodule
