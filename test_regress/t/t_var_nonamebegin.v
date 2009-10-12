module t (/*AUTOARG*/
   // Inputs
   clk, reset_l
   );

   input	clk;
   input	reset_l;

   reg 		inmod;

   generate
      if (1) begin
	 // Traces as genblk1.ingen
	 integer ingen;
	 initial $display("ingen: {mod}.genblk1 %m");
      end
   endgenerate

   integer 	 rawmod;

   initial begin
      begin
	 integer upa;
	 begin : d3nameda
	    // %m='.d3nameda'  var=_unnamed#.d3nameda.b1
	    integer d3a;
	    $display("d3a: {mod}.d3nameda %m");
	 end
      end
   end
   initial begin
      integer b2;
      $display("b2: {mod} %m");
      begin : b3named
	 integer b3n;
	 $display("b3n: {mod}.b3named: %m");
      end
      if (1) begin
	 integer b3;
	 $display("b3: {mod} %m");
	 if (1) begin
	    begin
	       begin
		  begin
		     integer b4;
		     $display("b4: {mod} %m");
		  end
	       end
	    end
	 end
	 else begin
	    integer b4;
	    $display("bb %m");
	 end
      end
      else begin
	 integer b4;
	 $display("b4 %m");
      end
      tsk;
      $write("*-* All Finished *-*\n");
      $finish;
   end

   task tsk;
      integer t1;
      $display("t1 {mod}.tsk %m");
      begin
	 integer t2;
	 $display("t2 {mod}.tsk %m");
      end
   endtask

endmodule
