// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2008 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   reg   toggle;
   initial toggle=0;

   integer cyc;
   initial cyc=1;

   wire [7:0] cyc_copy = cyc[7:0];

   alpha a1 (/*AUTOINST*/
             // Inputs
             .clk                       (clk),
             .toggle                    (toggle));
   alpha a2 (/*AUTOINST*/
             // Inputs
             .clk                       (clk),
             .toggle                    (toggle));
   beta  b1 (/*AUTOINST*/
             // Inputs
             .clk                       (clk),
             .toggle                    (toggle));
   beta  b2 (/*AUTOINST*/
             // Inputs
             .clk                       (clk),
             .toggle                    (toggle));
   tsk   t1 (/*AUTOINST*/
             // Inputs
             .clk                       (clk),
             .toggle                    (toggle));
   off   o1 (/*AUTOINST*/
             // Inputs
             .clk                       (clk),
             .toggle                    (toggle));

   always @ (posedge clk) begin
      if (cyc!=0) begin
         cyc <= cyc + 1;
         toggle <= '0;
         // Single and multiline if
         if (cyc==3) $write("");
         if (cyc==3)
           begin
              $write("");
           end
         // Single and multiline else
         if (cyc==3) ; else $write("");
         if (cyc==3) ;
         else
           begin
              $write("");
           end
         // Single and multiline if else
         if (cyc==3) $write(""); else $write("");
         if (cyc==3)
           begin
              $write("");
           end
         else
           begin
              $write("");
           end
         //  multiline elseif
         if (cyc==3)
           begin
              $write("");
           end
         else if (cyc==4)
           begin
              $write("");
           end
         else if (cyc==5)
           begin
              $write("");
           end
         else
           begin
              $write("");
           end
         // Single and multiline while
         while (0);
         while (0) begin
            $write("");
         end
         do ; while (0);
         do begin
            $write("");
         end while (0);
         //===
         // Task and complicated
         if (cyc==3) begin
            toggle <= '1;
         end
         else if (cyc==5) begin
`ifdef VERILATOR
            $c("this->call_task();");
`else
            call_task();
`endif
         end
         else if (cyc==10) begin
            $write("*-* All Finished *-*\n");
            $finish;
         end
      end
   end

   task call_task;
      /* verilator public */
      t1.center_task(1'b1);
   endtask

endmodule

module alpha (/*AUTOARG*/
   // Inputs
   clk, toggle
   );
   input clk;
   input toggle;
   always @ (posedge clk) begin
      if (toggle) begin  // CHECK_COVER(0,"top.t.a*",2)
         $write("");
         // t.a1 and t.a2 collapse to a count of 2
      end
      if (toggle) begin
         $write("");  // CHECK_COVER_MISSING(0)
         // This doesn't even get added
`ifdef ATTRIBUTE
         // verilator coverage_block_off
`endif
      end
   end
endmodule

module beta (/*AUTOARG*/
   // Inputs
   clk, toggle
   );
   input clk;
   input toggle;

   /* verilator public_module */

   always @ (posedge clk) begin
      $write("");  // Always covered
      if (0) begin  // CHECK_COVER(0,"top.t.b*",0)
         // Make sure that we don't optimize away zero buckets
         $write("");
      end
      if (toggle) begin  // CHECK_COVER(0,"top.t.b*",2)
         // t.b1 and t.b2 collapse to a count of 2
         $write("");
      end
      if (toggle) begin : block
         // This doesn't
`ifdef ATTRIBUTE
         // verilator coverage_block_off
`endif
         begin end  // Needed for .vlt to attach coverage_block_off
         if (1) begin end  // CHECK_COVER_MISSING(0)
         $write("");  // CHECK_COVER_MISSING(0)
      end
   end
endmodule

module tsk (/*AUTOARG*/
   // Inputs
   clk, toggle
   );
   input clk;
   input toggle;

   /* verilator public_module */

   always @ (posedge clk) begin
      center_task(1'b0);
   end

   task center_task;
      input external;
      begin
         if (toggle) begin  // CHECK_COVER(0,"top.t.t1",1)
            $write("");
         end
         if (external) begin  // CHECK_COVER(0,"top.t.t1",1)
            $write("[%0t] Got external pulse\n", $time);
         end
      end
   endtask

endmodule

module off (/*AUTOARG*/
   // Inputs
   clk, toggle
   );
   input clk;
   input toggle;

   // verilator coverage_off
   always @ (posedge clk) begin
      if (toggle) begin
         $write("");  // CHECK_COVER_MISSING(0)
         // because under coverage_module_off
      end
   end
   // verilator coverage_on
   always @ (posedge clk) begin
      if (toggle) begin
         // because under coverage_module_off
         $write("");
         if (0) ;  // CHECK_COVER(0,"top.t.o1",1)
      end
   end

endmodule
