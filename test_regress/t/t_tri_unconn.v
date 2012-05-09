// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer 	cyc=0;

   wire  one = '1;
   wire  z0 = 'z;
   wire  z1 = 'z;
   wire  z2 = 'z;
   wire  z3 = 'z;
   wire  tog = cyc[0];

   // verilator lint_off PINMISSING
   t_tri0 tri0a (.line(`__LINE__), .expval(1'b0)); // Pin missing
   t_tri0 tri0b (.line(`__LINE__), .expval(1'b0),    .tn());
   t_tri0 tri0z (.line(`__LINE__), .expval(1'b0),    .tn(z0));
   t_tri0 tri0Z (.line(`__LINE__), .expval(1'b0),    .tn(1'bz));
   t_tri0 tri0c (.line(`__LINE__), .expval(1'b0),    .tn(1'b0));
   t_tri0 tri0d (.line(`__LINE__), .expval(1'b1),    .tn(1'b1));  // Warning would be reasonable given tri0 connect
   t_tri0 tri0e (.line(`__LINE__), .expval(1'b0),    .tn(~one));
   t_tri0 tri0f (.line(`__LINE__), .expval(1'b1),    .tn(one));
   t_tri0 tri0g (.line(`__LINE__), .expval(~cyc[0]), .tn(~tog));
   t_tri0 tri0h (.line(`__LINE__), .expval(cyc[0]),  .tn(tog));

   t_tri1 tri1a (.line(`__LINE__), .expval(1'b1)); // Pin missing
   t_tri1 tri1b (.line(`__LINE__), .expval(1'b1),    .tn());
   t_tri1 tri1z (.line(`__LINE__), .expval(1'b1),    .tn(z1));
   t_tri1 tri1Z (.line(`__LINE__), .expval(1'b1),    .tn(1'bz));
   t_tri1 tri1c (.line(`__LINE__), .expval(1'b0),    .tn(1'b0));  // Warning would be reasonable given tri1 connect
   t_tri1 tri1d (.line(`__LINE__), .expval(1'b1),    .tn(1'b1));
   t_tri1 tri1e (.line(`__LINE__), .expval(1'b0),    .tn(~one));
   t_tri1 tri1f (.line(`__LINE__), .expval(1'b1),    .tn(one));
   t_tri1 tri1g (.line(`__LINE__), .expval(~cyc[0]), .tn(~tog));
   t_tri1 tri1h (.line(`__LINE__), .expval(cyc[0]),  .tn(tog));

   t_tri2 tri2a (.line(`__LINE__), .expval(1'b0)); // Pin missing
   t_tri2 tri2b (.line(`__LINE__), .expval(1'b0),    .tn());
   t_tri2 tri2z (.line(`__LINE__), .expval(1'b0),    .tn(z2));
   t_tri2 tri2Z (.line(`__LINE__), .expval(1'b0),    .tn(1'bz));
   t_tri2 tri2c (.line(`__LINE__), .expval(1'b0),    .tn(1'b0));
   t_tri2 tri2d (.line(`__LINE__), .expval(1'b1),    .tn(1'b1));
   t_tri2 tri2e (.line(`__LINE__), .expval(1'b0),    .tn(~one));
   t_tri2 tri2f (.line(`__LINE__), .expval(1'b1),    .tn(one));
   t_tri2 tri2g (.line(`__LINE__), .expval(~cyc[0]), .tn(~tog));
   t_tri2 tri2h (.line(`__LINE__), .expval(cyc[0]),  .tn(tog));

   t_tri3 tri3a (.line(`__LINE__), .expval(1'b1)); // Pin missing
   t_tri3 tri3b (.line(`__LINE__), .expval(1'b1),    .tn());
   t_tri3 tri3z (.line(`__LINE__), .expval(1'b1),    .tn(z3));
   t_tri3 tri3Z (.line(`__LINE__), .expval(1'b1),    .tn(1'bz));
   t_tri3 tri3c (.line(`__LINE__), .expval(1'b0),    .tn(1'b0));
   t_tri3 tri3d (.line(`__LINE__), .expval(1'b1),    .tn(1'b1));
   t_tri3 tri3e (.line(`__LINE__), .expval(1'b0),    .tn(~one));
   t_tri3 tri3f (.line(`__LINE__), .expval(1'b1),    .tn(one));
   t_tri3 tri3g (.line(`__LINE__), .expval(~cyc[0]), .tn(~tog));
   t_tri3 tri3h (.line(`__LINE__), .expval(cyc[0]),  .tn(tog));
   // verilator lint_on PINMISSING

   // Test loop
   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc==99) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule

module t_tri0
  (line, expval, tn);
   input integer line;
   input expval;
   input tn;  // Illegal to be inout; spec requires net connection to any inout
   tri0  tn;
   wire  clk = t.clk;
   always @(posedge clk) if (tn !== expval) begin
      $display("%%Error: from line %0d got=%x exp=%x",line,tn,expval); $stop;
   end
endmodule

module t_tri1
  (line, expval, tn);
   input integer line;
   input expval;
   input tn;
   tri1  tn;
   wire  clk = t.clk;
   always @(posedge clk) if (tn !== expval) begin
      $display("%%Error: from line %0d got=%x exp=%x",line,tn,expval); $stop;
   end
endmodule

module t_tri2
  (line, expval, tn);
   input integer line;
   input expval;
   input tn;
   pulldown(tn);
   wire  clk = t.clk;
   always @(posedge clk) if (tn !== expval) begin
      $display("%%Error: from line %0d got=%x exp=%x",line,tn,expval); $stop;
   end
endmodule

module t_tri3
  (line, expval, tn);
   input integer line;
   input expval;
   input tn;
   pullup(tn);
   wire  clk = t.clk;
   always @(negedge clk) if (tn !== expval) begin
      $display("%%Error: from line %0d got=%x exp=%x",line,tn,expval); $stop;
   end
endmodule
