// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   integer cyc; initial cyc=1;

   // Life analysis checks
   reg [15:0] life;

   // Ding case
   reg [7:0]  din;
   reg [15:0] fixin;
   always @* begin
      fixin = {din[7:0],din[7:0]};
      case (din[1:0])
        2'b00: begin
           fixin = {fixin[14:0], 1'b1};
           if (cyc==101) $display("Prevent ?: optimization a");
        end
        2'b01: begin
           fixin = {fixin[13:0], 2'b11};
           if (cyc==101) $display("Prevent ?: optimization b");
        end
        2'b10: begin
           fixin = {fixin[12:0], 3'b111};
           if (cyc==101) $display("Prevent ?: optimization c");
        end
        2'b11: begin
           fixin = {fixin[11:0], 4'b1111};
           if (cyc==101) $display("Prevent ?: optimization d");
        end
      endcase
   end

   always @ (posedge clk) begin
      if (cyc!=0) begin
         cyc<=cyc+1;
         if (cyc==1) begin
            life = 16'h8000;    // Dropped
            life = 16'h0010;    // Used below
            if (life != 16'h0010) $stop;
            //
            life = 16'h0020;    // Used below
            if ($time < 10000)
              if (life != 16'h0020) $stop;
            //
            life = 16'h8000;    // Dropped
            if ($time > 100000) begin
               if ($time != 0) $stop;   // Prevent conversion to ?:
               life = 16'h1030;
            end
            else
                life = 16'h0030;
            if (life != 16'h0030) $stop;
            //
            life = 16'h0040;    // Not dropped, no else below
            if ($time > 100000)
              life = 16'h1040;
            if (life != 16'h0040) $stop;
            //
            life = 16'h8000;    // Dropped
            if ($time > 100000) begin
               life = 16'h1050;
               if (life != 0) $stop;  // Ignored, as set is first
            end
            else begin
               if ($time > 100010)
                 life = 16'h1050;
               else life = 16'h0050;
            end
            if (life != 16'h0050) $stop;
         end
         if (cyc==2) begin
            din <= 8'haa;
         end
         if (cyc==3) begin
            din <= 8'hfb;
            if (fixin != 16'h5557) $stop;
         end
         if (cyc==4) begin
            din <= 8'h5c;
            if (fixin != 16'hbfbf) $stop;
         end
         if (cyc==5) begin
            din <= 8'hed;
            if (fixin != 16'hb8b9) $stop;
         end
         if (cyc==6) begin
            if (fixin != 16'hb7b7) $stop;
         end
         if (cyc==9) begin
            $write("*-* All Finished *-*\n");
            $finish;
         end
      end
   end
endmodule
