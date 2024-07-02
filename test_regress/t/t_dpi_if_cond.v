// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2024 by Antmicro. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module t (/*AUTOARG*/
  // Inputs
  clk
  );

  input clk;

  integer counter = 0;
  import "DPI-C" context function int  dpii_increment(inout int counter);

  function void func();
  endfunction : func

  always @(posedge clk) begin
    if(dpii_increment(counter) == 1) begin
      // unreachable
      func();

      // add impure statement for splitting
      $write("");
    end
    else if (counter == 1) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
    else begin
      $write("DPI called too many times: %d\n", counter);
      $stop;
    end
  end
endmodule
