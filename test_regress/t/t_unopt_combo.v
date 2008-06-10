// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2005 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   integer cyc; initial cyc=0;
   reg [63:0] crc;
   reg [63:0] sum;

`ifdef ALLOW_UNOPT
   /*verilator lint_off UNOPTFLAT*/
`endif

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [31:0]		b;			// From file of file.v
   wire [31:0]		c;			// From file of file.v
   wire [31:0]		d;			// From file of file.v
   // End of automatics

   file file (/*AUTOINST*/
	      // Outputs
	      .b			(b[31:0]),
	      .c			(c[31:0]),
	      .d			(d[31:0]),
	      // Inputs
	      .crc			(crc[31:0]));

   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc=%0d crc=%x sum=%x b=%x d=%x\n",$time,cyc,crc,sum, b, d);
`endif
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63]^crc[2]^crc[0]};
      sum <= {b, d}
	     ^ {sum[62:0],sum[63]^sum[2]^sum[0]};
      if (cyc==0) begin
	 // Setup
	 crc <= 64'h5aef0c8d_d70a4497;
      end
      else if (cyc<10) begin
	 sum <= 64'h0;
      end
      else if (cyc<90) begin
      end
      else if (cyc==99) begin
	 $write("*-* All Finished *-*\n");
	 $write("[%0t] cyc==%0d crc=%x %x\n",$time, cyc, crc, sum);
	 if (crc !== 64'hc77bb9b3784ea091) $stop;
	 if (sum !== 64'h649ee1713d624dd9) $stop;
	 $finish;
      end
   end

endmodule

module file (/*AUTOARG*/
   // Outputs
   b, c, d,
   // Inputs
   crc
   );

   input [31:0]        crc;
`ifdef ISOLATE
   output reg [31:0]   b /* verilator isolate_assignments*/;
`else
   output reg [31:0]   b;
`endif

   output reg [31:0]   c;
   output reg [31:0]   d;

   always @* begin
      // Note that while c and b depend on crc, b doesn't depend on c.
      casez (crc[3:0])
	4'b??01: begin
	   b = {crc[15:0],get_31_16(crc)};
	   d = c;
	end
	4'b??00: begin
	   b = {crc[15:0],~crc[31:16]};
	   d = {crc[15:0],~c[31:16]};
	end
	default: begin
	   set_b_d(crc, c);
	end
      endcase
   end

   function [31:16] get_31_16	/* verilator isolate_assignments*/;
      input [31:0] t_crc	/* verilator isolate_assignments*/;
      get_31_16 = t_crc[31:16];
   endfunction

   task set_b_d;
`ifdef ISOLATE
      input [31:0] t_crc	/* verilator isolate_assignments*/;
      input [31:0] t_c		/* verilator isolate_assignments*/;
`else
      input [31:0] t_crc;
      input [31:0] t_c;
`endif
      begin
	 b = {t_crc[31:16],~t_crc[23:8]};
	 d = {t_crc[31:16],  ~t_c[23:8]};
      end
   endtask

   always @* begin
      // Any complicated equation we can't optimize
      casez (crc[3:0])
	4'b00??: begin
	   c = {b[29:0],2'b11};
	end
	4'b01??: begin
	   c = {b[30:1],2'b01};
	end
	4'b10??: begin
	   c = {b[31:2],2'b10};
	end
	4'b11??: begin
	   c = {b[31:2],2'b00};
	end
      endcase
   end

endmodule
