// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2012 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   tri z0;
   tri z1;

   updown #(0) updown0 (.z(z0));
   updown #(1) updown1 (.z(z1));

   always @ (posedge clk) begin
      if (z0 !== 0) $stop;
      if (z1 !== 1) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule

module updown #(parameter UP=0)
   (inout z);
   generate
      if (UP) begin
	 t_up sub (.z);
      end
      else begin
	 t_down sub (.z);
      end
   endgenerate
endmodule

module t_up (inout tri1 z);
endmodule

module t_down (inout tri0 z);
endmodule
