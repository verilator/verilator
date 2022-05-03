// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2010 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`ifndef VERILATOR
module t;
   /*AUTOREGINPUT*/
   // Beginning of automatic reg inputs (for undeclared instantiated-module inputs)
   reg                  c0;                     // To t2 of t2.v
   reg                  c1;                     // To t2 of t2.v
   reg                  check;                  // To t2 of t2.v
   reg [1:0]            clks;                   // To t2 of t2.v
   // End of automatics
   t2 t2 (/*AUTOINST*/
          // Inputs
          .clks                         (clks[1:0]),
          .c0                           (c0),
          .c1                           (c1),
          .check                        (check));
   task clockit (input v1, v0);
      c1 = v1;
      c0 = v0;
      clks[1] = v1;
      clks[0] = v0;
 `ifdef TEST_VERBOSE $write("[%0t] c1=%x c0=%x\n", $time,v0,v1); `endif
      #1;
   endtask
   initial begin
      check = '0;
      c0 = '0;
      c1 = '0;
      clks = '0;
      #1
      t2.clear();
      #10;
      for (int i=0; i<2; i++) begin
         clockit(0, 0);
         clockit(0, 0);
         clockit(0, 1);
         clockit(1, 1);
         clockit(0, 0);
         clockit(1, 1);
         clockit(1, 0);
         clockit(0, 0);
         clockit(1, 0);
         clockit(0, 1);
         clockit(0, 0);
      end
      check = 1;
      clockit(0, 0);
   end
endmodule
`endif

`ifdef VERILATOR
 `define t2 t
`else
 `define t2 t2
`endif

module `t2 (
          input [1:0] clks,
          input       c0,
          input       c1,
          input check
   );

`ifdef T_CLK_2IN_VEC
   wire    clk0 = clks[0];
   wire    clk1 = clks[1];
`else
   wire    clk0 = c0;
   wire    clk1 = c1;
`endif

   integer p0 = 0;
   integer p1 = 0;
   integer p01 = 0;
   integer n0 = 0;
   integer n1 = 0;
   integer n01 = 0;
   integer vp = 0;
   integer vn = 0;
   integer vpn = 0;
   task clear;
`ifdef TEST_VERBOSE $display("[%0t] clear\n", $time); `endif
      p0 = 0;
      p1 = 0;
      p01 = 0;
      n0 = 0;
      n1 = 0;
      n01 = 0;
      vp = 0;
      vn = 0;
      vpn = 0;
   endtask

`define display_counts(text) begin \
   $write("[%0t] ", $time); \
   `ifdef T_CLK_2IN_VEC $write(" 2v "); `endif \
   $write(text); \
   $write(": %0d %0d %0d  %0d %0d %0d  %0d %0d %0d\n",  p0, p1, p01,  n0, n1, n01,  vp, vn, vpn); \
   end

   always @ (posedge clk0) begin
      p0 = p0 + 1;  // Want blocking, so don't miss clock counts
`ifdef TEST_VERBOSE `display_counts("posedge 0"); `endif
   end
   always @ (posedge clk1) begin
      p1 = p1 + 1;
`ifdef TEST_VERBOSE `display_counts("posedge 1"); `endif
   end
   always @ (posedge clk0 or posedge clk1) begin
      p01 = p01 + 1;
`ifdef TEST_VERBOSE `display_counts("posedge *"); `endif
   end

   always @ (negedge clk0) begin
      n0 = n0 + 1;
`ifdef TEST_VERBOSE `display_counts("negedge 0"); `endif
   end
   always @ (negedge clk1) begin
      n1 = n1 + 1;
`ifdef TEST_VERBOSE `display_counts("negedge 1"); `endif
   end
   always @ (negedge clk0 or negedge clk1) begin
      n01 = n01 + 1;
`ifdef TEST_VERBOSE `display_counts("negedge *"); `endif
   end

`ifndef VERILATOR
   always @ (posedge clks) begin
      vp = vp + 1;
`ifdef TEST_VERBOSE `display_counts("pos   vec"); `endif
   end
   always @ (negedge clks) begin
      vn = vn + 1;
`ifdef TEST_VERBOSE `display_counts("neg   vec"); `endif
   end
   always @ (posedge clks or negedge clks) begin
      vpn = vpn + 1;
`ifdef TEST_VERBOSE `display_counts("or    vec"); `endif
   end
`endif

   always @ (posedge check) begin
      if (p0!=6) $stop;
      if (p1!=6) $stop;
      if (p01!=10) $stop;
      if (n0!=6) $stop;
      if (n1!=6) $stop;
      if (n01!=10) $stop;
`ifndef VERILATOR
      if (vp!=6) $stop;
      if (vn!=6) $stop;
      if (vpn!=12) $stop;
`endif
      $write("*-* All Finished *-*\n");
   end

endmodule
