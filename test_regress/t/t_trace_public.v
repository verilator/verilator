// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2008 by Wilson Snyder.

module t (
    input  wire CLK,
    output reg  RESET
	  );

   glbl glbl;

   initial RESET = 1'b1;
   always @ (posedge CLK)
     RESET <= glbl.GSR;

endmodule

module glbl();
`ifdef PUB_FUNC
   wire GSR;
   task setGSR;
      /* verilator public */
      input value;
      GSR = value;
   endtask
`else
   wire GSR /*verilator public*/;
`endif
endmodule
