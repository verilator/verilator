// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2004 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   // Check empty blocks
   task EmptyFor;
      /* verilator public */
      integer i;
      begin
         for (i = 0; i < 2; i = i+1)
           begin
           end
      end
   endtask

   // Check look unroller
   reg signed      signed_tests_only = 1'sb1;
   integer         total;

   integer         i;
   reg [31:0]      iu;
   reg [31:0]      dly_to_ensure_was_unrolled [1:0];
   reg [2:0]       i3;

   integer cyc; initial cyc = 0;
   always @ (posedge clk) begin
      cyc <= cyc + 1;
      case (cyc)
        1: begin
           // >= signed
           total = 0;
           for (i=5; i>=0; i=i-1) begin
              total = total - i -1;
              dly_to_ensure_was_unrolled[i] <= i;
           end
           if (total != -21) $stop;
        end
        2: begin
           // > signed
           total = 0;
           for (i=5; i>0; i=i-1) begin
              total = total - i -1;
              dly_to_ensure_was_unrolled[i] <= i;
           end
           if (total != -20) $stop;
        end
        3: begin
           // < signed
           total = 0;
           for (i=1; i<5; i=i+1) begin
              total = total - i -1;
              dly_to_ensure_was_unrolled[i] <= i;
           end
           if (total != -14) $stop;
        end
        4: begin
           // <= signed
           total = 0;
           for (i=1; i<=5; i=i+1) begin
              total = total - i -1;
              dly_to_ensure_was_unrolled[i] <= i;
           end
           if (total != -20) $stop;
        end
        // UNSIGNED
        5: begin
           // >= unsigned
           total = 0;
           for (iu=5; iu>=1; iu=iu-1) begin
              total = total - iu -1;
              dly_to_ensure_was_unrolled[iu] <= iu;
           end
           if (total != -20) $stop;
        end
        6: begin
           // > unsigned
           total = 0;
           for (iu=5; iu>1; iu=iu-1) begin
              total = total - iu -1;
              dly_to_ensure_was_unrolled[iu] <= iu;
           end
           if (total != -18) $stop;
        end
        7: begin
           // < unsigned
           total = 0;
           for (iu=1; iu<5; iu=iu+1) begin
              total = total - iu -1;
              dly_to_ensure_was_unrolled[iu] <= iu;
           end
           if (total != -14) $stop;
        end
        8: begin
           // <= unsigned
           total = 0;
           for (iu=1; iu<=5; iu=iu+1) begin
              total = total - iu -1;
              dly_to_ensure_was_unrolled[iu] <= iu;
           end
           if (total != -20) $stop;
        end
        //===
        9: begin
           // mostly cover a small index
           total = 0;
           for (i3=3'd0; i3<3'd7; i3=i3+3'd1) begin
              total = total - {29'd0,i3} -1;
              dly_to_ensure_was_unrolled[i3[0]] <= 0;
           end
           if (total != -28) $stop;
        end
        //===
        10: begin
           // mostly cover a small index
           total = 0;
           for (i3=0; i3<3'd7; i3=i3+3'd1) begin
              total = total - {29'd0,i3} -1;
              dly_to_ensure_was_unrolled[i3[0]] <= 0;
           end
           if (total != -28) $stop;
        end
        //===
        11: begin
           // width violation on <, causes extend
           total = 0;
           for (i3=3'd0; i3<7; i3=i3+1) begin
              total = total - {29'd0,i3} -1;
              dly_to_ensure_was_unrolled[i3[0]] <= 0;
           end
           if (total != -28) $stop;
        end
        //===
        // width violation on <, causes extend signed
        // Unsupported as yet
        //===
        19: begin
           $write("*-* All Finished *-*\n");
           $finish;
        end
        default: ;
      endcase
   end
endmodule
