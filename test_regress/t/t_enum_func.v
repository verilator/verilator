// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2010 by Wilson Snyder.

typedef enum { EN_ZERO,
	       EN_ONE
	       } En_t;

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   // Insure that we can declare a type with a function declaration
   function enum integer {
			  EF_TRUE = 1,
			  EF_FALSE = 0 }
				    f_enum_inv ( input a);
      f_enum_inv = a ? EF_FALSE : EF_TRUE;
   endfunction
   initial begin
      if (f_enum_inv(1) != 0) $stop;
      if (f_enum_inv(0) != 1) $stop;
   end

   En_t a, z;

   sub sub (/*AUTOINST*/
	    // Outputs
	    .z				(z),
	    // Inputs
	    .a				(a));

   integer    cyc; initial cyc=1;
   always @ (posedge clk) begin
      if (cyc!=0) begin
	 cyc <= cyc + 1;
	 if (cyc==1) begin
	    a <= EN_ZERO;
	 end
	 if (cyc==2) begin
	    a <= EN_ONE;
	    if (z != EN_ONE) $stop;
	 end
	 if (cyc==3) begin
	    if (z != EN_ZERO) $stop;
	 end
	 if (cyc==9) begin
	    $write("*-* All Finished *-*\n");
	    $finish;
	 end
      end
   end

endmodule

module sub (input En_t a, output En_t z);
   always @* z = (a==EN_ONE) ? EN_ZERO : EN_ONE;
endmodule

// Local Variables:
// verilog-typedef-regexp: "_t$"
// End:
