module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   localparam string TEST_STRING = "test";
   localparam CHECK_DECREMENT = decrement_array_idx();
   localparam CHECK_INCREMENT = increment_array_idx();

   function byte decrement_array_idx();
      int pos = TEST_STRING.len() - 1;
      decrement_array_idx = TEST_STRING[--pos];
   endfunction

   function byte increment_array_idx();
      int pos = 0;
      increment_array_idx = TEST_STRING[++pos];
   endfunction

   initial begin
      if (CHECK_DECREMENT != "s") $stop;
      if (CHECK_INCREMENT != "e") $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
