// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2008 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   reg 	 toggle; initial toggle=0;

   integer cyc; initial cyc=1;
   wire [7:0] cyc_copy = cyc[7:0];

   alpha a1 (/*AUTOINST*/
	     // Inputs
	     .clk			(clk),
	     .toggle			(toggle));
   alpha a2 (/*AUTOINST*/
	     // Inputs
	     .clk			(clk),
	     .toggle			(toggle));
   beta  b1 (/*AUTOINST*/
	     // Inputs
	     .clk			(clk),
	     .toggle			(toggle));
   beta  b2 (/*AUTOINST*/
	     // Inputs
	     .clk			(clk),
	     .toggle			(toggle));
   tsk   t1 (/*AUTOINST*/
	     // Inputs
	     .clk			(clk),
	     .toggle			(toggle));
   off   o1 (/*AUTOINST*/
	     // Inputs
	     .clk			(clk),
	     .toggle			(toggle));

   always @ (posedge clk) begin
      if (cyc!=0) begin
	 cyc <= cyc + 1;
	 toggle <= '0;
	 if (cyc==3) begin
	    toggle <= '1;
	 end
	 else if (cyc==5) begin
`ifdef VERILATOR
	    $c("call_task();");
`else
	    call_task();
`endif
	 end
	 else if (cyc==10) begin
	    $write("*-* All Finished *-*\n");
	    $finish;
	 end
      end
   end

   task call_task;
      /* verilator public */
      t1.center_task(1'b1);
   endtask

endmodule

module alpha (/*AUTOARG*/
   // Inputs
   clk, toggle
   );
   input clk;
   input toggle;
   always @ (posedge clk) begin
      if (toggle) begin
	 // CHECK_COVER(-1,"top.v.a*",2)
	 // t.a1 and t.a2 collapse to a count of 2
      end
      if (toggle) begin
	 // CHECK_COVER_MISSING(-1)
	 // This doesn't even get added
	 // verilator coverage_block_off
	 $write("");
      end
   end
endmodule

module beta (/*AUTOARG*/
   // Inputs
   clk, toggle
   );
   input clk;
   input toggle;

   /* verilator public_module */

   always @ (posedge clk) begin
      if (0) begin
	 // CHECK_COVER(-1,"top.v.b*",0)
	 // Make sure that we don't optimize away zero buckets
      end
      if (toggle) begin
	 // CHECK_COVER(-1,"top.v.b*",2)
	 // t.b1 and t.b2 collapse to a count of 2
      end
      if (toggle) begin
	 // CHECK_COVER_MISSING(-1)
	 // This doesn't
	 // verilator coverage_block_off
	 $write("");
      end
   end
endmodule

module tsk (/*AUTOARG*/
   // Inputs
   clk, toggle
   );
   input clk;
   input toggle;

   /* verilator public_module */

   always @ (posedge clk) begin
      center_task(1'b0);
   end

   task center_task;
      input external;
      begin
	 if (toggle) begin
	    // CHECK_COVER(-1,"top.v.t1",1)
	 end
	 if (external) begin
	    // CHECK_COVER(-1,"top.v.t1",1)
	    $write("[%0t] Got external pulse\n", $time);
	 end
      end
   endtask

endmodule

module off (/*AUTOARG*/
   // Inputs
   clk, toggle
   );
   input clk;
   input toggle;

   // verilator coverage_off
   always @ (posedge clk) begin
      if (toggle) begin
	 // CHECK_COVER_MISSING(-1)
	 // because under coverage_module_off
      end
   end
   // verilator coverage_on
   always @ (posedge clk) begin
      if (toggle) begin
	 // CHECK_COVER(-1,"top.v.o1",1)
	 // because under coverage_module_off
      end
   end

endmodule
