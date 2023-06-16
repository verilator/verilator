module t();
   std::process proc;
   logic clk = 0;
   logic b = 0;

   always #1 clk = ~clk;

   task kill_me_after_1ns(std::process proc);
      fork
         #1 proc.kill(); // kill proc after 1 step
         #3 begin        // finish after the next clock cycle
            $write("*-* All Finished *-*\n");
            $finish;
         end
      join_none
   endtask

   always @(posedge clk) begin
      if (!b) begin
         proc = std::process::self();
         kill_me_after_1ns(proc);
         b = 1;
      end else begin
         $stop;
      end
   end
endmodule
