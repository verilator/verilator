// DESCRIPTION: Verilator: Verilog Test module
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2008 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer 	cyc=0;
   integer	v;

   reg 	i;
   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire			oa;			// From a of a.v
   wire			oz;			// From z of z.v
   // End of automatics

   a a (.*);
   z z (.*);

   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d i=%x oa=%x oz=%x\n",$time, cyc, i, oa, oz);
`endif
      cyc <= cyc + 1;
      i <= cyc[0];
      if (cyc==0) begin
	 v = 3;
	 if (v !== 3) $stop;
	 if (assignin(v) !== 2) $stop;
	 if (v !== 3) $stop; // Make sure V didn't get changed
      end
      else if (cyc<10) begin
	 if (cyc==11 && oz!==1'b0)  $stop;
	 if (cyc==12 && oz!==1'b1)  $stop;
	 if (cyc==12 && oa!==1'b1)  $stop;
      end
      else if (cyc<90) begin
      end
      else if (cyc==99) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

   function integer assignin(input integer i);
      i = 2;
      assignin = i;
   endfunction 

endmodule

module a (input i, output oa);
   // verilator lint_off ASSIGNIN
   assign i = 1'b1;
   assign oa = i;
endmodule

module z (input i, output oz);
   assign oz = i;
endmodule
