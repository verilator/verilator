// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2018 by Julien Margetts.
// SPDX-License-Identifier: CC0-1.0

module t #(parameter sz = 4096)
   (
    input wire                     clk,
    output reg [tdw(sz)-1:0] data
    );

   // bug1330
   function integer clog2(input integer value);
      integer tmp;
      tmp   = value-1;
      clog2 = 0;
      for (clog2=0; (tmp>0) && (clog2<32); clog2=clog2+1)
        tmp = tmp>>1;
   endfunction

   function integer tdw(input integer sz);
      tdw = clog2(sz);
   endfunction

   integer b;

   always @(posedge clk)
     for (b=0; b<tdw(sz); b=b+1)
       if ((data[b] === 1'bx))
         $display("WARNING: %1t Writing X's to tag RAM [%m]", $time);

endmodule
