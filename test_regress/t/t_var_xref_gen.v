// DESCRIPTION: Verilator: Verilog Test module
//
// This is to test the handling of VarXRef when the referenced VAR is
// under a generate construction.
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2015 by Jie Xu and Roland Kruse.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
	  // Inputs
	  clk, addr, res
	  );

   input clk;

   input [31:0] addr;
   output [15:0] res;

   memory i_mem(.addr(addr),.dout(res));

   assign i_mem.cxrow_inst[0].cmem_xrow[0] = 16'h0;

endmodule



module memory(addr, dout);
   parameter CM_XROWSIZE = 256;
   parameter CM_NUMXROWS = 2;

   input [31:0] addr;
   output [15:0] dout;

   generate
      genvar 	 g_cx;
      for (g_cx = 0; g_cx < CM_NUMXROWS; g_cx++)
        begin: cxrow_inst
           reg [15:0] cmem_xrow[0:CM_XROWSIZE - 1];
        end
   endgenerate

   assign dout = cxrow_inst[0].cmem_xrow[addr];
endmodule
