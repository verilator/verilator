// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2018 Julien Margetts
// SPDX-License-Identifier: CC0-1.0

module t #(parameter SZ = 4096)
   (
    input wire                     clk,
    output reg [tdw(SZ)-1:0] data
    );

   // bug1330
   function integer clog2(input integer value);
      integer tmp;
      tmp   = value-1;
      clog2 = 0;
      for (clog2=0; (tmp>0) && (clog2<32); clog2=clog2+1)
        tmp = tmp>>1;
   endfunction

   function integer tdw(input integer SZ);
      tdw = clog2(SZ);
   endfunction

   integer b;

   always @(posedge clk)
     for (b=0; b<tdw(SZ); b=b+1)
       if ((data[b] === 1'bx))
         $display("WARNING: %1t Writing X's to tag RAM [%m]", $time);

endmodule
