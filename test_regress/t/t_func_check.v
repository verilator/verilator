// DESCRIPTION: Verilator: Verilog Test module
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// verilator lint_off WIDTH
// verilator lint_off VARHIDDEN

module t (
   clk
   );
   input clk;
   integer      cyc = 0;
   reg [63:0]   crc; initial crc = 64'h1;

   chk chk (.clk        (clk),
            .rst_l      (1'b1),
            .expr       (|crc)
            );

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
      if (cyc==0) begin
         crc <= 64'h5aef0c8d_d70a4497;
      end
      else if (cyc<90) begin
      end
      else if (cyc==99) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule

module chk (input clk, input rst_l, input expr);

   integer errors; initial errors = 0;

   task printerr;
      input [8*64:1] msg;
      begin
         errors = errors + 1;
         $write("%%Error: %0s\n", msg);
         $stop;
      end
   endtask

   always @(posedge clk) begin
      if (rst_l) begin
         if (expr == 1'b0) begin
            printerr("expr not asserted");
         end
      end
   end

   wire noxs = ((expr ^ expr) == 1'b0);

   reg    hasx;
   always @ (noxs) begin
      if (noxs) begin
         hasx = 1'b0;
      end
      else begin
         hasx = 1'b1;
      end
   end

   always @(posedge clk) begin
      if (rst_l) begin
         if (hasx) begin
            printerr("expr has unknowns");
         end
      end
   end

endmodule
