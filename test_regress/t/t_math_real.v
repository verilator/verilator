// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2011 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

`define is_near_real(a,b)  (( ((a)<(b)) ? (b)-(a) : (a)-(b)) < (((a)/(b))*0.0001))

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer i;
   reg [63:0] b;
   real  r, r2;
   integer      cyc=0;

   realtime  uninit;
   initial if (uninit != 0.0) $stop;

   sub_cast_bug374 sub (.cyc5(cyc[4:0]), .*);

   initial begin
      if (1_00_0.0_1 != 1000.01) $stop;
      // rtoi truncates
      if ($rtoi(36.7) != 36) $stop;
      if ($rtoi(36.5) != 36) $stop;
      if ($rtoi(36.4) != 36) $stop;
      // casting rounds
      if ((integer '(36.7)) != 37) $stop;
      if ((integer '(36.5)) != 37) $stop;
      if ((integer '(36.4)) != 36) $stop;
      // assignment rounds
      // verilator lint_off REALCVT
      i = 36.7; if (i != 37) $stop;
      i = 36.5; if (i != 37) $stop;
      i = 36.4; if (i != 36) $stop;
      r = 10'd38;  if (r!=38.0) $stop;
      // verilator lint_on REALCVT
      // operators
      if ((-(1.5)) != -1.5) $stop;
      if ((+(1.5)) != 1.5) $stop;
      if (((1.5)+(1.25)) != 2.75) $stop;
      if (((1.5)-(1.25)) != 0.25) $stop;
      if (((1.5)*(1.25)) != 1.875) $stop;
      if (((1.5)/(1.25)) != 1.2) $stop;
      //
      if (((1.5)==(2)) != 1'b0) $stop;  // note 2 becomes real 2.0
      if (((1.5)!=(2)) != 1'b1) $stop;
      if (((1.5)> (2)) != 1'b0) $stop;
      if (((1.5)>=(2)) != 1'b0) $stop;
      if (((1.5)< (2)) != 1'b1) $stop;
      if (((1.5)<=(2)) != 1'b1) $stop;
      if (((1.5)==(1.5)) != 1'b1) $stop;
      if (((1.5)!=(1.5)) != 1'b0) $stop;
      if (((1.5)> (1.5)) != 1'b0) $stop;
      if (((1.5)>=(1.5)) != 1'b1) $stop;
      if (((1.5)< (1.5)) != 1'b0) $stop;
      if (((1.5)<=(1.5)) != 1'b1) $stop;
      if (((1.6)==(1.5)) != 1'b0) $stop;
      if (((1.6)!=(1.5)) != 1'b1) $stop;
      if (((1.6)> (1.5)) != 1'b1) $stop;
      if (((1.6)>=(1.5)) != 1'b1) $stop;
      if (((1.6)< (1.5)) != 1'b0) $stop;
      if (((1.6)<=(1.5)) != 1'b0) $stop;
      //
      if (((0.0)?(2.0):(1.1)) != 1.1) $stop;
      if (((1.5)?(2.0):(1.1)) != 2.0) $stop;
      //
      if (!1.7) $stop;
      if (!(!0.0)) $stop;
      if (1.8 && 0.0) $stop;
      if (!(1.8 || 0.0)) $stop;
      //
      i=0;
      for (r=1.0; r<2.0; r=r+0.1) i++;
      if (i!=10) $stop;
      // bug
      r = $bitstoreal($realtobits(1.414));
      if (r != 1.414) $stop;
   end

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d crc=%x result=%x\n",$time, cyc, crc, result);
`endif
      cyc <= cyc + 1;
      if (cyc==0) begin
         // Setup
      end
      else if (cyc<90) begin
         if ($time != {32'h0, $rtoi($realtime)}) $stop;
         if ($itor(cyc) != cyc) $stop;
         //Unsup: if ((real `($time)) != $realtime) $stop;
         r = $itor(cyc*2);
         i = $rtoi(r);
         if (i!=cyc*2) $stop;
         //
         r = $itor(cyc)/1.5;
         b = $realtobits(r);
         r2 = $bitstoreal(b);
         if (r != r2) $stop;
         //
         // Trust the integer math as a comparison
         r = $itor(cyc);
         if ($rtoi(-r) != -cyc) $stop;
         if ($rtoi(+r) != cyc) $stop;
         if ($rtoi(r+2.0) != (cyc+2)) $stop;
         if ($rtoi(r-2.0) != (cyc-2)) $stop;
         if ($rtoi(r*2.0) != (cyc*2)) $stop;
         if ($rtoi(r/2.0) != (cyc/2)) $stop;
         r2 = (2.0/(r-60));  // When zero, result indeterminate, but no crash
         //
         r2 = $itor(cyc);
         case (r)
           (r2-1.0): $stop;
           r2: ;
           default: $stop;
         endcase
         //
         r = $itor(cyc);
         if ((r==50.0) != (cyc==50)) $stop;
         if ((r!=50.0) != (cyc!=50)) $stop;
         if ((r> 50.0) != (cyc> 50)) $stop;
         if ((r>=50.0) != (cyc>=50)) $stop;
         if ((r< 50.0) != (cyc< 50)) $stop;
         if ((r<=50.0) != (cyc<=50)) $stop;
         //
         if ($rtoi((r-50.0) ? 10.0 : 20.0)
             !=  (((cyc-50)!=0) ? 10 : 20)) $stop;
         //
         if ((!(r-50.0)) != (!((cyc-50) != 0))) $stop;
      end
      else if (cyc==99) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule

module sub_cast_bug374(input clk, input [4:0] cyc5);
    integer i;

    always @(posedge clk) begin
       i <= integer'(cyc5);
    end
endmodule
