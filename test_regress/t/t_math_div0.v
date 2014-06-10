module t(y);
   output [3:0] y;
   // bug775
   // verilator lint_off WIDTH
   assign y = ((0/0) ? 1 : 2) % 0;

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
