// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2008 by Lane Brooks

module t (clk);
   input clk;

   reg [31:0] state;  initial state=0;

   wire A = state[0];
   wire OE = state[1];
   wire Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8, Z9;
   
   Test1 test1(/*AUTOINST*/
	       // Inouts
	       .Z1			(Z1),
	       // Inputs
	       .OE			(OE),
	       .A			(A));

   Test2 test2(/*AUTOINST*/
	       // Inouts
	       .Z2			(Z2),
	       // Inputs
	       .OE			(OE),
	       .A			(A));

   Test3 test3(/*AUTOINST*/
	       // Inouts
	       .Z3			(Z3),
	       // Inputs
	       .OE			(OE),
	       .A			(A));

   Test4 test4(/*AUTOINST*/
	       // Outputs
	       .Z4			(Z4),
	       // Inouts
	       .Z5			(Z5));

   Test5 test5(/*AUTOINST*/
	       // Inouts
	       .Z6			(Z6),
	       .Z7			(Z7),
	       .Z8			(Z8),
	       .Z9			(Z9),
	       // Inputs
	       .OE			(OE));
   
   
   always @(posedge clk) begin
      state <= state + 1;
`ifdef TEST_VERBOSE
      $display(" Z1=%b 2=%b 3=%b 4=%b 5=%b 6=%b 7=%b 8=%b 9=%b",Z1,Z2,Z3,Z4,Z5,Z6,Z7,Z8,Z9);
`endif

      if(state == 0) begin
	 if(Z1 !== 1'b1) $stop;  // tests pullups
	 if(Z2 !== 1'b1) $stop;
	 if(Z3 !== 1'b1) $stop;
	 if(Z4 !== 1'b1) $stop;
	 if(Z5 !== 1'b1) $stop;
	 if(Z6 !== 1'b1) $stop;
	 if(Z7 !== 1'b0) $stop;
	 if(Z8 !== 1'b0) $stop;
	 if(Z9 !== 1'b1) $stop;
      end 
      else if(state == 1) begin
	 if(Z1 !== 1'b1) $stop;  // tests pullup
	 if(Z2 !== 1'b1) $stop;
	 if(Z3 !== 1'b1) $stop;
	 if(Z4 !== 1'b1) $stop;
	 if(Z5 !== 1'b1) $stop;
	 if(Z6 !== 1'b1) $stop;
	 if(Z7 !== 1'b0) $stop;
	 if(Z8 !== 1'b0) $stop;
	 if(Z9 !== 1'b1) $stop;
      end
      else if(state == 2) begin
	 if(Z1 !== 1'b0) $stop; // tests output driver low
	 if(Z2 !== 1'b0) $stop;
	 //if(Z3 !== 1'b1) $stop;   // "X"
	 if(Z4 !== 1'b1) $stop;
	 if(Z5 !== 1'b1) $stop;
	 if(Z6 !== 1'b0) $stop;
	 if(Z7 !== 1'b1) $stop;
	 if(Z8 !== 1'b1) $stop;
	 if(Z9 !== 1'b0) $stop;
      end
      else if(state == 3) begin
	 if(Z1 !== 1'b1) $stop; // tests output driver high
	 if(Z2 !== 1'b1) $stop;
	 if(Z3 !== 1'b1) $stop;
	 if(Z4 !== 1'b1) $stop;
	 if(Z5 !== 1'b1) $stop;
	 if(Z6 !== 1'b0) $stop;
	 if(Z7 !== 1'b1) $stop;
	 if(Z8 !== 1'b1) $stop;
	 if(Z9 !== 1'b0) $stop;
      end 
      else if(state == 4) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end
   pullup(Z1);
   pullup(Z2);
   pullup(Z3);
   pullup(Z4);
   pullup(Z5);
   pullup(Z6);
   pulldown(Z7);
   pullup(Z8);
   pulldown(Z9);
endmodule


module Test1(input OE, input A, inout Z1);
   assign Z1 = (OE) ? A : 1'bz;
endmodule

module Test2(input OE, input A, inout Z2);
   assign Z2 = (OE) ? A : 1'bz;
endmodule


// mixed low-Z and tristate
module Test3(input OE, input A, inout Z3);
   assign Z3 = (OE) ? A : 1'bz;
   assign Z3 = 1'b1;
endmodule


// floating output and inout
module Test4(output Z4, inout Z5);
endmodule


// AND gate tristates
module Test5(input OE, inout Z6, inout Z7, inout Z8, inout Z9);
   assign Z6 = (OE) ? 1'b0 : 1'bz;
   assign Z7 = (OE) ? 1'b1 : 1'bz;
   assign Z8 = (OE) ? 1'bz : 1'b0;
   assign Z9 = (OE) ? 1'bz : 1'b1;
endmodule


// This is not implemented yet
//module Test3(input OE, input A, inout Z3);
//   always @(*) begin
//      if(OE) begin
//	 Z3 = A;
//      end else begin
//	 Z3 = 1'bz;
//      end
//   end
//endmodule

