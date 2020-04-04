// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2015 by Johan Bjork.
// SPDX-License-Identifier: CC0-1.0

module t;
   localparam str = "string";
   function logic checkParameter(input logic [8:0] N);
      $display("x is %d.", N);
      if (N == 1)
        return 0;
      $fatal(1, "Parameter %d is invalid...%s and %s", N, str, "constant both work");
   endfunction

`ifdef FAILING_ASSERTIONS
   localparam x = checkParameter(5);
`else
   localparam x = checkParameter(1);
`endif

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
