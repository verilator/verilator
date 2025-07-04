// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t (  /*AUTOARG*/);
  for (genvar j = 0; j < 3; j++) begin : genblk
    initial begin : init
      int i;
      begin : named
        for (i = 0; i < 10; ++i) begin : loop
          if (i == 5) disable named;
        end
      end
      if (i != 5) $stop;
    end
  end
  initial begin
    #1;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
