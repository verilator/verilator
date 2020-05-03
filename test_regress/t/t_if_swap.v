module t
  (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   integer f;

   always @(posedge clk) begin
      if (!$feof(f)) begin
         $display("Doing stuff with file.");
      end
      // Commenting out these two lines fixes the fault
      else begin
      end
      if (!$feof(f)) begin
      end
      else begin
         $display("Not doing stuff with file.");
      end
   end

endmodule
