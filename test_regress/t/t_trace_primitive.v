// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2014 by Jie Xu.

module t
  (
   clk
   );

   input clk;
   integer    cyc; initial cyc = 0;

   reg a;
   reg b;
   reg z;
   sub_t sub_t_i (z, a, b);

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      a <= cyc[0];
      b <= cyc[1];

      if (cyc > 10) begin
          $write("*-* All Finished *-*\n");
          $finish;
      end
   end
endmodule

primitive CINV (a, b);
output b;
input a;
assign b = ~a;
endprimitive


module sub_t (z, x, y);
input x, y;
output z;

assign z = x & y;
endmodule
