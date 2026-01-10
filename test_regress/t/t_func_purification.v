// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t;
  initial begin
    if (0 & func(1)) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
  function bit func(bit x);
    if (x) begin
      if (x) begin
        return 1;
      end
      else begin
        $c("");
      end
      return 0;
    end
  endfunction
endmodule
