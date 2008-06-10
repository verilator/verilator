// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2005 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   // Some inputs we'll set to random values
   reg [6:0] addr;
   reg [6:0] e0;
   reg [5:0] e1;
   reg [5:0] e2;

   wire [7:0] data;
   reg [2:0]  wrapcheck_a;
   reg [2:0]  wrapcheck_b;

   test test  (/*AUTOINST*/
	       // Outputs
	       .data			(data[7:0]),
	       // Inputs
	       .addr			(addr[6:0]),
	       .e0			(e0[6:0]),
	       .e1			(e1[5:0]),
	       .e2			(e2[5:0]));

   always @(/*AS*/addr) begin
      case(addr[2:0])
	3'd0+3'd0:  wrapcheck_a = 3'h0;
	3'd0+3'd1:  wrapcheck_a = 3'h1;
	3'd0+3'd2:  wrapcheck_a = 3'h2;
	3'd0+3'd3:  wrapcheck_a = 3'h3;
	default:    wrapcheck_a = 3'h4;
      endcase

      case(addr[2:0])
	3'd0+0:  wrapcheck_b = 3'h0;
	3'd1+1:  wrapcheck_b = 3'h1;
	3'd2+2:  wrapcheck_b = 3'h2;
	3'd3+3:  wrapcheck_b = 3'h3;
	default: wrapcheck_b = 3'h4;
      endcase
   end

   integer    cyc; initial cyc=1;
   always @ (posedge clk) begin
      if (cyc!=0) begin
	 cyc <= cyc + 1;
	 //$write("%d %x %x %x\n", cyc, data, wrapcheck_a, wrapcheck_b);
	 if (cyc==1) begin
	    addr <= 7'h28;
	    e0 <= 7'h11;
	    e1 <= 6'h02;
	    e2 <= 6'h03;
	 end
	 if (cyc==2) begin
	    addr <= 7'h2b;
	    if (data != 8'h11) $stop;
	 end
	 if (cyc==3) begin
	    addr <= 7'h2c;
	    if (data != 8'h03) $stop;
	    if (wrapcheck_a != 3'h3) $stop;
	    if (wrapcheck_b != 3'h4) $stop;
	 end
	 if (cyc==4) begin
	    addr <= 7'h0;
	    if (data != 8'h00) $stop;
	    if (wrapcheck_a != 3'h4) $stop;
	    if (wrapcheck_b != 3'h2) $stop;
	 end
	 if (cyc==5) begin
	    if (data != 8'h00) $stop;
	 end
	 if (cyc==9) begin
	    $write("*-* All Finished *-*\n");
	    $finish;
	 end
      end
   end

endmodule

/* verilator lint_off WIDTH */
`define AI    7'h28

module test (/*AUTOARG*/
   // Outputs
   data,
   // Inputs
   addr, e0, e1, e2
   );

   output [7:0]	data;

   input [6:0] 	addr;
   input [6:0] 	e0;
   input [5:0] 	e1, e2;

   reg [7:0] 	data;

   always @(/*AS*/addr or e0 or e1 or e2)
     begin
    	case (addr)
	  `AI:   data = {e0[6], 1'b0, e0[5:0]};
	  `AI+1: data = e1;
	  `AI+2,
	  `AI+3: data = e2;
	  default:   data = 0;
    	endcase
     end

endmodule

// Local Variables:
// eval:(verilog-read-defines)
// verilog-auto-sense-defines-constant: t
// End:
