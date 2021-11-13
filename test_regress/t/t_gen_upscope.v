// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2012 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

/* Acceptable answer 1
created tag with scope = top.t.tag
created tag with scope = top.t.b.gen[0].tag
created tag with scope = top.t.b.gen[1].tag
mod a has scope = top.t
mod a has tag   = top.t.tag
mod b has scope = top.t.b
mod b has tag   = top.t.tag
mod c has scope = top.t.b.gen[0].c
mod c has tag   = top.t.b.gen[0].tag
mod c has scope = top.t.b.gen[1].c
mod c has tag   = top.t.b.gen[1].tag
*/
/* Acceptable answer 2
created tag with scope = top.t.tag
created tag with scope = top.t.b.gen[0].tag
created tag with scope = top.t.b.gen[1].tag
mod a has scope = top.t
mod a has tag   = top.t.tag
mod b has scope = top.t.b
mod b has tag   = top.t.tag
mod c has scope = top.t.b.gen[0].c
mod c has tag   = top.t.tag
mod c has scope = top.t.b.gen[1].c
mod c has tag   = top.t.tag
*/

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;
   integer      cyc = 0;

   tag tag ();
   b b ();

   always @ (t.cyc) begin
      if (t.cyc == 2) $display("mod a has scope = %m");
      if (t.cyc == 2) $display("mod a has tag   = %0s", tag.scope);
   end

   always @(posedge clk) begin
      cyc <= cyc + 1;
      if (cyc==99) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule

module b ();
   genvar g;
   generate
      for (g=0; g<2; g++) begin : gen
         tag tag ();
         c c ();
      end
   endgenerate
   always @ (t.cyc) begin
      if (t.cyc == 3) $display("mod b has scope = %m");
      if (t.cyc == 3) $display("mod b has tag   = %0s", tag.scope);
   end
endmodule

module c ();
   always @ (t.cyc) begin
      if (t.cyc == 4) $display("mod c has scope = %m");
      if (t.cyc == 4) $display("mod c has tag   = %0s", tag.scope);
   end
endmodule

module tag ();
   bit [100*8-1:0] scope;
   initial begin
      $sformat(scope,"%m");
      $display("created tag with scope = %0s",scope);
   end
endmodule
