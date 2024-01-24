// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2005 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define STRINGIFY(x) `"x`"

`define stop $stop
`ifdef VERILATOR
 `define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
`else
 `define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); end while(0)
`endif

module t (/*AUTOARG*/
   // Outputs
   out_data
   );

   output [11:0] out_data;
   wire [11:0]   out_data;
   wire [11:0]   a;
   wire [2:0]    b;
   assign a = 12'h000 ** { b };
   assign b = 3'b0;
   assign out_data = a;

endmodule
