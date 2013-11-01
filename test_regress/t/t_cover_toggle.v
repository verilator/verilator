// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2008 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   typedef struct packed {
      union packed {
	 logic 	  ua;
	 logic 	  ub;
      } u;
      logic b;
   } str_t;

   reg 	 toggle; initial toggle='0;

   str_t stoggle; initial stoggle='0;

   const reg aconst = '0;

   reg [1:0][1:0] ptoggle; initial ptoggle=0;

   integer cyc; initial cyc=1;
   wire [7:0] cyc_copy = cyc[7:0];
   wire       toggle_up;

   alpha a1 (/*AUTOINST*/
	     // Outputs
	     .toggle_up			(toggle_up),
	     // Inputs
	     .clk			(clk),
	     .toggle			(toggle),
	     .cyc_copy			(cyc_copy[7:0]));
   alpha a2 (/*AUTOINST*/
	     // Outputs
	     .toggle_up			(toggle_up),
	     // Inputs
	     .clk			(clk),
	     .toggle			(toggle),
	     .cyc_copy			(cyc_copy[7:0]));

   beta  b1 (/*AUTOINST*/
	     // Inputs
	     .clk			(clk),
	     .toggle_up			(toggle_up));

   off   o1 (/*AUTOINST*/
	     // Inputs
	     .clk			(clk),
	     .toggle			(toggle));

   reg [1:0]  memory[121:110];

   reg [1023:0] largeish;
   // CHECK_COVER_MISSING(-1)

   always @ (posedge clk) begin
      if (cyc!=0) begin
	 cyc <= cyc + 1;
	 memory[cyc + 'd100] <= memory[cyc + 'd100] + 2'b1;
	 toggle <= '0;
	 stoggle.u <= toggle;
	 stoggle.b <= toggle;
	 ptoggle[0][0] <= toggle;
	 if (cyc==3) begin
	    toggle <= '1;
	 end
	 if (cyc==4) begin
	    toggle <= '0;
	 end
	 else if (cyc==10) begin
	    $write("*-* All Finished *-*\n");
	    $finish;
	 end
      end
   end

endmodule

module alpha (/*AUTOARG*/
   // Outputs
   toggle_up,
   // Inputs
   clk, toggle, cyc_copy
   );

   // t.a1 and t.a2 collapse to a count of 2

   input clk;

   input toggle;
   // CHECK_COVER(-1,"top.v.a*",4)
   // 2 edges * (t.a1 and t.a2)

   input [7:0] cyc_copy;
   // CHECK_COVER(-1,"top.v.a*","cyc_copy[0]",22)
   // CHECK_COVER(-2,"top.v.a*","cyc_copy[1]",10)
   // CHECK_COVER(-3,"top.v.a*","cyc_copy[2]",4)
   // CHECK_COVER(-4,"top.v.a*","cyc_copy[3]",2)
   // CHECK_COVER(-5,"top.v.a*","cyc_copy[4]",0)
   // CHECK_COVER(-6,"top.v.a*","cyc_copy[5]",0)
   // CHECK_COVER(-7,"top.v.a*","cyc_copy[6]",0)
   // CHECK_COVER(-8,"top.v.a*","cyc_copy[7]",0)

   reg 	       toggle_internal;
   // CHECK_COVER(-1,"top.v.a*",4)
   // 2 edges * (t.a1 and t.a2)

   output reg  toggle_up;
   // CHECK_COVER(-1,"top.v.a*",4)
   // 2 edges * (t.a1 and t.a2)

   always @ (posedge clk) begin
      toggle_internal <= toggle;
      toggle_up       <= toggle;
   end
endmodule

module beta (/*AUTOARG*/
   // Inputs
   clk, toggle_up
   );

   input clk;

   input toggle_up;
   // CHECK_COVER(-1,"top.v.b1","toggle_up",2)

   /* verilator public_module */

   always @ (posedge clk) begin
      if (0 && toggle_up) begin end
   end
endmodule

module off (/*AUTOARG*/
   // Inputs
   clk, toggle
   );

   // verilator coverage_off
   input clk;
   // CHECK_COVER_MISSING(-1)

   // verilator coverage_on
   input toggle;
   // CHECK_COVER(-1,"top.v.o1","toggle",2)

endmodule
