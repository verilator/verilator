// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2010 by Wilson Snyder.

module t;

   integer v = 19;

   initial begin
      if (v==1) begin end
      else if (v==2) begin end
      else if (v==3) begin end
      else if (v==4) begin end
      else if (v==5) begin end
      else if (v==6) begin end
      else if (v==7) begin end
      else if (v==8) begin end
      else if (v==9) begin end
      else if (v==10) begin end
      else if (v==11) begin end  // Warn about this one
      else if (v==12) begin end
   end

   initial begin
      unique0 if (v==1) begin end
      else if (v==2) begin end
      else if (v==3) begin end
      else if (v==4) begin end
      else if (v==5) begin end
      else if (v==6) begin end
      else if (v==7) begin end
      else if (v==8) begin end
      else if (v==9) begin end
      else if (v==10) begin end
      else if (v==11) begin end  // Warn about this one
      else if (v==12) begin end
   end

endmodule
