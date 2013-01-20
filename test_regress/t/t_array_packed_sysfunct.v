// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2009 by Iztok Jeras.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

`define check(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: Line%0d: cnt=0x%0x  got=0x%0x exp=0x%0x\n", `__LINE__, cnt, (gotv), (expv)); $stop; end while(0);

   // parameters for array sizes
   localparam WA = 4;
   localparam WB = 6;
   localparam WC = 8;

   // 2D packed arrays
   logic [WA+1:2] [WB+1:2] [WC+1:2] array_bg;  // big endian array
   /* verilator lint_off LITENDIAN */
   logic [2:WA+1] [2:WB+1] [2:WC+1] array_lt;  // little endian array
   /* verilator lint_on LITENDIAN */

   logic [1:0] array_unpk [3:2][1:0];

   integer cnt = 0;
   integer slc = 0;  // slice type
   integer dim = 0;  // dimension
   integer wdt = 0;  // width

   initial begin
      `check($dimensions (array_unpk), 3);
`ifndef VCS
      `check($unpacked_dimensions (array_unpk), 2);  // IEEE 2009
`endif
      `check($bits (array_unpk), 2*2*2);
      `check($low  (array_unpk), 2);
      `check($high (array_unpk), 3);
      `check($left (array_unpk), 3);
      `check($right(array_unpk), 2);
      `check($increment(array_unpk), 1);
      `check($size (array_unpk), 2);
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
	 // big endian
	 if (slc==0) begin
            // full array
            `check($dimensions (array_bg), 3);
            `check($bits       (array_bg), WA*WB*WC);
            if ((dim>=1)&&(dim<=3)) begin
               `check($left       (array_bg, dim), wdt+1);
               `check($right      (array_bg, dim), 2    );
               `check($low        (array_bg, dim), 2    );
               `check($high       (array_bg, dim), wdt+1);
               `check($increment  (array_bg, dim), 1    );
               `check($size       (array_bg, dim), wdt  );
            end
	 end else if (slc==1) begin
            // single array element
            `check($dimensions (array_bg[2]), 2);
            `check($bits       (array_bg[2]), WB*WC);
            if ((dim>=2)&&(dim<=3)) begin
               `check($left       (array_bg[2], dim-1), wdt+1);
               `check($right      (array_bg[2], dim-1), 2    );
               `check($low        (array_bg[2], dim-1), 2    );
               `check($high       (array_bg[2], dim-1), wdt+1);
               `check($increment  (array_bg[2], dim-1), 1    );
               `check($size       (array_bg[2], dim-1), wdt  );
            end
`ifndef VERILATOR // Unsupported slices don't maintain size correctly
	 end else if (slc==2) begin
            // half array
            `check($dimensions (array_bg[WA/2+1:2]), 3);
            `check($bits       (array_bg[WA/2+1:2]), WA/2*WB*WC);
            if ((dim>=1)&&(dim<=3)) begin
               `check($left       (array_bg[WA/2+1:2], dim), wdt+1);
               `check($right      (array_bg[WA/2+1:2], dim), 2    );
               `check($low        (array_bg[WA/2+1:2], dim), 2    );
               `check($high       (array_bg[WA/2+1:2], dim), wdt+1);
               `check($increment  (array_bg[WA/2+1:2], dim), 1    );
               `check($size       (array_bg[WA/2+1:2], dim), wdt);
            end
`endif
	 end
      end else if (cnt[30:4]==2) begin
	 // little endian
	 if (slc==0) begin
            // full array
            `check($dimensions (array_lt), 3);
            `check($bits       (array_lt), WA*WB*WC);
            if ((dim>=1)&&(dim<=3)) begin
               `check($left       (array_lt, dim), 2    );
               `check($right      (array_lt, dim), wdt+1);
               `check($low        (array_lt, dim), 2    );
               `check($high       (array_lt, dim), wdt+1);
               `check($increment  (array_lt, dim), -1   );
               `check($size       (array_lt, dim), wdt  );
            end
	 end else if (slc==1) begin
            // single array element
            `check($dimensions (array_lt[2]), 2);
            `check($bits       (array_lt[2]), WB*WC);
            if ((dim>=2)&&(dim<=3)) begin
               `check($left       (array_lt[2], dim-1), 2    );
               `check($right      (array_lt[2], dim-1), wdt+1);
               `check($low        (array_lt[2], dim-1), 2    );
               `check($high       (array_lt[2], dim-1), wdt+1);
               `check($increment  (array_lt[2], dim-1), -1   );
               `check($size       (array_lt[2], dim-1), wdt  );
            end
`ifndef VERILATOR // Unsupported slices don't maintain size correctly
	 end else if (slc==2) begin
            // half array
            `check($dimensions (array_lt[2:WA/2+1]), 3);
            `check($bits       (array_lt[2:WA/2+1]), WA/2*WB*WC);
            if ((dim>=1)&&(dim<=3)) begin
               `check($left       (array_lt[2:WA/2+1], dim), 2    );
               `check($right      (array_lt[2:WA/2+1], dim), wdt+1);
               `check($low        (array_lt[2:WA/2+1], dim), 2    );
               `check($high       (array_lt[2:WA/2+1], dim), wdt+1);
               `check($increment  (array_lt[2:WA/2+1], dim), -1   );
               `check($size       (array_lt[2:WA/2+1], dim), wdt  );
            end
`endif
	 end
      end
   end
   
endmodule
