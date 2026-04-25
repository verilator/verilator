// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   integer cyc; initial cyc = 0;

   wire q;
   logic d=0, clear, preset;

   dff flipflop(q, d, clear, preset, clk);

   //clear and preset signals are in inverted logic
   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if(cyc==0) begin
         clear=1;
         preset=0;
         d=0;
      end
      else if(cyc==1) begin
         `checkh(q, 1);
         preset=1;
         d=1;
      end
      else if(cyc==2) begin
         `checkh(q, 1);
         clear=0;
      end
      else if(cyc==3) begin
         `checkh(q, 0);
         preset=0;
      end
      else if(cyc==4) begin
         `checkh(q, 0);
         clear=1;
         preset=1;
      end
      else if(cyc==5) begin
         `checkh(q, 1);
         d=0;
      end
      else if(cyc==6) begin
         `checkh(q, 0);
         d=1;
      end
      else if(cyc==7) begin
         `checkh(q, 1);
      end
      else if (cyc==8) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule

// From IEEE 1800-2023 10.6.1

module dff (q, d, clear, preset, clock);
   output q;
   input d, clear, preset, clock;
   logic q;

   always @(clear or preset)
      if (!clear)
         assign q = 0;
      else if (!preset)
         assign q = 1;
      else
         deassign q;
   always @(posedge clock)
      q = d;
endmodule
