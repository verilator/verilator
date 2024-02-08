// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2009 by Iztok Jeras.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   // parameters for array sizes
   localparam WA = 4;
   localparam WB = 6;
   localparam WC = 8;

   // 2D packed arrays
   logic [WA+1:2] [WB+1:2] [WC+1:2] array_dsc;  // descending range array
   /* verilator lint_off ASCRANGE */
   logic [2:WA+1] [2:WB+1] [2:WC+1] array_asc;  // ascending range array
   /* verilator lint_on ASCRANGE */

   logic [1:0] array_unpk [3:2][1:0];

   integer cnt = 0;
   integer slc = 0;  // slice type
   integer dim = 0;  // dimension
   integer wdt = 0;  // width

   initial begin
      `checkh($dimensions (array_unpk), 3);
`ifndef VCS
      `checkh($unpacked_dimensions (array_unpk), 2);  // IEEE 2009
`endif
      `checkh($bits (array_unpk), 2*2*2);
      `checkh($low  (array_unpk), 2);
      `checkh($high (array_unpk), 3);
      `checkh($left (array_unpk), 3);
      `checkh($right(array_unpk), 2);
      `checkh($increment(array_unpk), 1);
      `checkh($size (array_unpk), 2);
   end

   // event counter
   always @ (posedge clk) begin
      cnt <= cnt + 1;
   end

   // finish report
   always @ (posedge clk)
   if ( (cnt[30:4]==3) && (cnt[3:2]==2'd3) && (cnt[1:0]==2'd3) ) begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

   integer slc_next;

   // calculation of dimention sizes
   always @ (posedge clk) begin
      // slicing type counter
      case (cnt[3:2])
         2'd0   : begin  slc_next = 0;  end  // full array
         2'd1   : begin  slc_next = 1;  end  // single array element
         2'd2   : begin  slc_next = 2;  end  // half array
         default: begin  slc_next = 0;  end
      endcase
      slc <= slc_next;
      // dimension counter
      case (cnt[1:0])
         2'd0   : begin  dim <= 1;  wdt <= (slc_next==1) ? WA/2 : (slc_next==2) ? WA/2 : WA;  end
         2'd1   : begin  dim <= 2;  wdt <= WB;  end
         2'd2   : begin  dim <= 3;  wdt <= WC;  end
         default: begin  dim <= 0;  wdt <= 0;   end
      endcase
   end

   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("cnt[30:4]=%0d slc=%0d dim=%0d wdt=%0d\n", cnt[30:4], slc, dim, wdt);
`endif
      if (cnt[30:4]==1) begin
         // descending range
         if (slc==0) begin
            // full array
            `checkh($dimensions (array_dsc), 3);
            `checkh($bits       (array_dsc), WA*WB*WC);
            if ((dim>=1)&&(dim<=3)) begin
               `checkh($left       (array_dsc, dim), wdt+1);
               `checkh($right      (array_dsc, dim), 2    );
               `checkh($low        (array_dsc, dim), 2    );
               `checkh($high       (array_dsc, dim), wdt+1);
               `checkh($increment  (array_dsc, dim), 1    );
               `checkh($size       (array_dsc, dim), wdt  );
            end
         end else if (slc==1) begin
            // single array element
            `checkh($dimensions (array_dsc[2]), 2);
            `checkh($bits       (array_dsc[2]), WB*WC);
            if ((dim>=2)&&(dim<=3)) begin
               `checkh($left       (array_dsc[2], dim-1), wdt+1);
               `checkh($right      (array_dsc[2], dim-1), 2    );
               `checkh($low        (array_dsc[2], dim-1), 2    );
               `checkh($high       (array_dsc[2], dim-1), wdt+1);
               `checkh($increment  (array_dsc[2], dim-1), 1    );
               `checkh($size       (array_dsc[2], dim-1), wdt  );
            end
`ifndef VERILATOR // Unsupported slices don't maintain size correctly
         end else if (slc==2) begin
            // half array
            `checkh($dimensions (array_dsc[WA/2+1:2]), 3);
            `checkh($bits       (array_dsc[WA/2+1:2]), WA/2*WB*WC);
            if ((dim>=1)&&(dim<=3)) begin
               `checkh($left       (array_dsc[WA/2+1:2], dim), wdt+1);
               `checkh($right      (array_dsc[WA/2+1:2], dim), 2    );
               `checkh($low        (array_dsc[WA/2+1:2], dim), 2    );
               `checkh($high       (array_dsc[WA/2+1:2], dim), wdt+1);
               `checkh($increment  (array_dsc[WA/2+1:2], dim), 1    );
               `checkh($size       (array_dsc[WA/2+1:2], dim), wdt);
            end
`endif
         end
      end else if (cnt[30:4]==2) begin
         // ascending range
         if (slc==0) begin
            // full array
            `checkh($dimensions (array_asc), 3);
            `checkh($bits       (array_asc), WA*WB*WC);
            if ((dim>=1)&&(dim<=3)) begin
               `checkh($left       (array_asc, dim), 2    );
               `checkh($right      (array_asc, dim), wdt+1);
               `checkh($low        (array_asc, dim), 2    );
               `checkh($high       (array_asc, dim), wdt+1);
               `checkh($increment  (array_asc, dim), -1   );
               `checkh($size       (array_asc, dim), wdt  );
            end
         end else if (slc==1) begin
            // single array element
            `checkh($dimensions (array_asc[2]), 2);
            `checkh($bits       (array_asc[2]), WB*WC);
            if ((dim>=2)&&(dim<=3)) begin
               `checkh($left       (array_asc[2], dim-1), 2    );
               `checkh($right      (array_asc[2], dim-1), wdt+1);
               `checkh($low        (array_asc[2], dim-1), 2    );
               `checkh($high       (array_asc[2], dim-1), wdt+1);
               `checkh($increment  (array_asc[2], dim-1), -1   );
               `checkh($size       (array_asc[2], dim-1), wdt  );
            end
`ifndef VERILATOR // Unsupported slices don't maintain size correctly
         end else if (slc==2) begin
            // half array
            `checkh($dimensions (array_asc[2:WA/2+1]), 3);
            `checkh($bits       (array_asc[2:WA/2+1]), WA/2*WB*WC);
            if ((dim>=1)&&(dim<=3)) begin
               `checkh($left       (array_asc[2:WA/2+1], dim), 2    );
               `checkh($right      (array_asc[2:WA/2+1], dim), wdt+1);
               `checkh($low        (array_asc[2:WA/2+1], dim), 2    );
               `checkh($high       (array_asc[2:WA/2+1], dim), wdt+1);
               `checkh($increment  (array_asc[2:WA/2+1], dim), -1   );
               `checkh($size       (array_asc[2:WA/2+1], dim), wdt  );
            end
`endif
         end
      end
   end

endmodule
