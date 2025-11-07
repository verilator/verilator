module t;
   timeunit 10s;
   timeprecision 1s;

   initial begin
      #1;
      if ($time != 1) $stop;
      repeat(10) #1step;
      if ($time != 2) $stop;
      #10;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
