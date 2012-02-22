module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;
   genvar g;
   generate
      for (g=0; g<1; g++)
	begin : picker
	   function [3:0] pick;
	      input [3:0]      randnum;
	      pick = randnum+g[3:0];
	   endfunction
	   always @(posedge clk) begin
	      if (pick(3)!=3+g[3:0]) $stop;
	      $write("*-* All Finished *-*\n");
	      $finish;
	   end
	end
   endgenerate
endmodule
