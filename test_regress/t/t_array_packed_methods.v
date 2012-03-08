// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012 by Iztok Jeras.

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
   logic [WA-1:0] [WB-1:0] [WC-1:0] array_bg;  // big endian array
   /* verilator lint_off LITENDIAN */
   logic [0:WA-1] [0:WB-1] [0:WC-1] array_lt;  // little endian array
   /* verilator lint_on LITENDIAN */

   integer cnt = 0;
   integer slc = 0;  // slice type
   integer dim = 0;  // dimension
   integer wdt = 0;  // width

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

   // calculation of dimention sizes
   always @ (posedge clk)
     begin
	// slicing tipe counter
	case (cnt[3:2])
          2'd0   : begin  slc = 0;  end  // full array
          2'd1   : begin  slc = 1;  end  // half array
          2'd2   : begin  slc = 2;  end  // single array element
          default: begin  slc = 0;  end
	endcase
	// dimmension counter
	case (cnt[1:0])
          2'd0   : begin  dim = 1;  wdt = (slc==1) ? WA/2
					  : (slc==2) ? 1
					  : WA;  end
          2'd1   : begin  dim = 2;  wdt = WB;  end
          2'd2   : begin  dim = 3;  wdt = WC;  end
          default: begin  dim = 0;  wdt = 0;   end
	endcase
     end

   always @ (posedge clk)
     if (cnt[30:4]==1) begin
	// big endian
	if (cnt[3:2]==0) begin
           // full array
           if ($dimensions (array_bg) != 3)        $stop;
           if ($bits       (array_bg) != WA*WB*WC) $stop;
           if ((dim>=1)&&(dim<=3)) begin
              if ($left       (array_bg, dim) != wdt-1) $stop;
              if ($right      (array_bg, dim) != 0    ) $stop;
              if ($low        (array_bg, dim) != 0    ) $stop;
              if ($high       (array_bg, dim) != wdt-1) $stop;
              if ($increment  (array_bg, dim) != 1    ) $stop;
              if ($size       (array_bg, dim) != wdt  ) $stop;
           end
	end else if (cnt[3:2]==1) begin
           // half array
           if ($dimensions (array_bg[WA/2-1:0]) != 3)          $stop;
           if ($bits       (array_bg[WA/2-1:0]) != WA/2*WB*WC) $stop;
           if ((dim>=1)&&(dim<=3)) begin
              if ($left       (array_bg[WA/2-1:0], dim) != wdt-1) $stop;
              if ($right      (array_bg[WA/2-1:0], dim) != 0    ) $stop;
              if ($low        (array_bg[WA/2-1:0], dim) != 0    ) $stop;
              if ($high       (array_bg[WA/2-1:0], dim) != wdt-1) $stop;
              if ($increment  (array_bg[WA/2-1:0], dim) != 1    ) $stop;
              if ($size       (array_bg[WA/2-1:0], dim) != wdt  ) $stop;
           end
	end else if (cnt[3:2]==2) begin
           // single array element
           if ($dimensions (array_bg[0]) != 2)     $stop;
           if ($bits       (array_bg[0]) != WB*WC) $stop;
           if ((dim>=2)&&(dim<=3)) begin
              if ($left       (array_bg[0], dim-1) != wdt-1) $stop;
              if ($right      (array_bg[0], dim-1) != 0    ) $stop;
              if ($low        (array_bg[0], dim-1) != 0    ) $stop;
              if ($high       (array_bg[0], dim-1) != wdt-1) $stop;
              if ($increment  (array_bg[0], dim-1) != 1    ) $stop;
              if ($size       (array_bg[0], dim-1) != wdt  ) $stop;
           end
	end
     end else if (cnt[30:4]==2) begin
	// little endian
	if (cnt[3:2]==0) begin
           // full array
           if ($dimensions (array_lt) != 3)        $stop;
           if ($bits       (array_lt) != WA*WB*WC) $stop;
           if ((dim>=1)&&(dim<=3)) begin
              if ($left       (array_lt, dim) != 0    ) $stop;
              if ($right      (array_lt, dim) != wdt-1) $stop;
              if ($low        (array_lt, dim) != 0    ) $stop;
              if ($high       (array_lt, dim) != wdt-1) $stop;
              if ($increment  (array_lt, dim) != -1   ) $stop;
              if ($size       (array_lt, dim) != wdt  ) $stop;
           end
	end else if (cnt[3:2]==1) begin
           // half array
           if ($dimensions (array_lt[0:WA/2-1]) != 3)          $stop;
           if ($bits       (array_lt[0:WA/2-1]) != WA/2*WB*WC) $stop;
           if ((dim>=1)&&(dim<=3)) begin
              if ($left       (array_lt[0:WA/2-1], dim) != 0    ) $stop;
              if ($right      (array_lt[0:WA/2-1], dim) != wdt-1) $stop;
              if ($low        (array_lt[0:WA/2-1], dim) != 0    ) $stop;
              if ($high       (array_lt[0:WA/2-1], dim) != wdt-1) $stop;
              if ($increment  (array_lt[0:WA/2-1], dim) != -1   ) $stop;
              if ($size       (array_lt[0:WA/2-1], dim) != wdt  ) $stop;
           end
	end else if (cnt[3:2]==2) begin
           // single array element
           if ($dimensions (array_lt[0]) != 2)     $stop;
           if ($bits       (array_lt[0]) != WB*WC) $stop;
           if ((dim>=2)&&(dim<=3)) begin
              if ($left       (array_lt[0], dim-1) != 0    ) $stop;
              if ($right      (array_lt[0], dim-1) != wdt-1) $stop;
              if ($low        (array_lt[0], dim-1) != 0    ) $stop;
              if ($high       (array_lt[0], dim-1) != wdt-1) $stop;
              if ($increment  (array_lt[0], dim-1) != -1   ) $stop;
              if ($size       (array_lt[0], dim-1) != wdt  ) $stop;
           end
	end
     end

endmodule
