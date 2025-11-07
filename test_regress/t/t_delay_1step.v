module t;
   timeunit 1s;
   timeprecision 1s;

   initial begin
      #1step;
      if ($time != 1) $stop;
      #10;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
