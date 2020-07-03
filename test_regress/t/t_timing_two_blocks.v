module top();

   initial begin
      if ($time != 0) $stop;

      #10;
      if ($time != 10) $stop;

      #10;
      if ($time != 20) $stop;

      #10;
      if ($time != 30) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

   initial begin
      #5;
      #10;
      #10;
   end
endmodule
