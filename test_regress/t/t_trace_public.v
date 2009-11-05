// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2008 by Wilson Snyder.

module t (
    input  wire CLK,
    output reg  RESET
	  );

   neg neg (.clk(CLK));
   little little (.clk(CLK));
   glbl glbl ();

   // A vector
   logic [2:1] vec [4:3];

   integer     val = 0;
   always @ (posedge CLK) begin
     if (RESET) val <= 0;
     else val <= val + 1;
      vec[3] <= val[1:0];
      vec[4] <= val[3:2];
   end

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

module neg (
   input clk
	    );

   reg [0:-7] i8; initial i8 = '0;
   reg [-1:-48] i48; initial i48 = '0;
   reg [63:-64] i128; initial i128 = '0;

   always @ (posedge clk) begin
      i8 <= ~i8;
      i48 <= ~i48;
      i128 <= ~i128;
   end
endmodule

module little (
   input clk
	    );

   // verilator lint_off LITENDIAN
   reg [0:7] i8; initial i8 = '0;
   reg [1:49] i48; initial i48 = '0;
   reg [63:190] i128; initial i128 = '0;
   // verilator lint_on LITENDIAN

   always @ (posedge clk) begin
      i8 <= ~i8;
      i48 <= ~i48;
      i128 <= ~i128;
   end
endmodule
