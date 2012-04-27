// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer 	cyc=0;

   wire  one = '1;
   wire  z0 = 'z;
   wire  z1 = 'z;
   wire  z2 = 'z;
   wire  z3 = 'z;

   // verilator lint_off PINMISSING
   t_tri0		   tri0a ();		// Error/warning
   t_tri0		   tri0b (.tn());
   t_tri0		   tri0z (.tn(z0));
   t_tri0 #(.EXPECT(1'b0)) tri0c (.tn(1'b0));
   t_tri0 #(.EXPECT(1'b1)) tri0d (.tn(1'b1));  // Warning would be reasonable given tri0 connect
   t_tri0 #(.EXPECT(1'b0)) tri0e (.tn(~one));
   t_tri0 #(.EXPECT(1'b1)) tri0f (.tn(one));

   t_tri1		   tri1a ();
   t_tri1		   tri1b (.tn());
   t_tri1		   tri1z (.tn(z1));
   t_tri1 #(.EXPECT(1'b0)) tri1c (.tn(1'b0));  // Warning would be reasonable given tri1 connect
   t_tri1 #(.EXPECT(1'b1)) tri1d (.tn(1'b1));
   t_tri1 #(.EXPECT(1'b0)) tri1e (.tn(~one));
   t_tri1 #(.EXPECT(1'b1)) tri1f (.tn(one));

   t_tri2		   tri2a ();
   t_tri2		   tri2b (.tn());
   t_tri2		   tri2z (.tn(z2));
   t_tri2 #(.EXPECT(1'b0)) tri2c (.tn(1'b0));
   t_tri2 #(.EXPECT(1'b1)) tri2d (.tn(1'b1));
   t_tri2 #(.EXPECT(1'b0)) tri2e (.tn(~one));
   t_tri2 #(.EXPECT(1'b1)) tri2f (.tn(one));

   t_tri3		   tri3a ();
   t_tri3		   tri3b (.tn());
   t_tri3		   tri3z (.tn(z3));
   t_tri3 #(.EXPECT(1'b0)) tri3c (.tn(1'b0));
   t_tri3 #(.EXPECT(1'b1)) tri3d (.tn(1'b1));
   t_tri3 #(.EXPECT(1'b0)) tri3e (.tn(~one));
   t_tri3 #(.EXPECT(1'b1)) tri3f (.tn(one));
   // verilator lint_on PINMISSING

   // Test loop
   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc==99) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule

module t_tri0
  #(parameter EXPECT=1'b0)
   (tn);
   input tn;  // Illegal to be inout; spec requires net connection to any inout
   tri0  tn;
   wire  clk = t.clk;
   always @(posedge clk) if (tn !== EXPECT) $stop;
endmodule

module t_tri1
  #(parameter EXPECT=1'b1)
   (tn);
   input tn;
   tri1  tn;
   wire  clk = t.clk;
   always @(posedge clk) if (tn !== EXPECT) $stop;
endmodule

module t_tri2
  #(parameter EXPECT=1'b0)
   (tn);
   input tn;
   pulldown(tn);
   wire  clk = t.clk;
   always @(posedge clk) if (tn !== EXPECT) $stop;
endmodule

module t_tri3
  #(parameter EXPECT=1'b1)
   (tn);
   input tn;
   pullup(tn);
   wire  clk = t.clk;
   always @(posedge clk) if (tn !== EXPECT) $stop;
endmodule
