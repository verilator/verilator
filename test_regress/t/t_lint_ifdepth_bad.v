// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2010 by Wilson Snyder.

module t;

   integer value = 19;

   initial begin
      if (value==1) begin end
      else if (value==2) begin end
      else if (value==3) begin end
      else if (value==4) begin end
      else if (value==5) begin end
      else if (value==6) begin end
      else if (value==7) begin end
      else if (value==8) begin end
      else if (value==9) begin end
      else if (value==10) begin end
      else if (value==11) begin end  // Warn about this one
      else if (value==12) begin end
   end

   initial begin
      unique0 if (value==1) begin end
      else if (value==2) begin end
      else if (value==3) begin end
      else if (value==4) begin end
      else if (value==5) begin end
      else if (value==6) begin end
      else if (value==7) begin end
      else if (value==8) begin end
      else if (value==9) begin end
      else if (value==10) begin end
      else if (value==11) begin end  // Warn about this one
      else if (value==12) begin end
   end

endmodule
