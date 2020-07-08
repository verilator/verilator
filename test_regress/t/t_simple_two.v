module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   initial begin
      $write("Simple first\n");
   end

   initial begin
      $write("Simple second\n");
      $write("*-* All Finished *-*\n");
      $finish;
   end

   always @ (posedge clk) begin
      $write("clk event");
   end
endmodule
