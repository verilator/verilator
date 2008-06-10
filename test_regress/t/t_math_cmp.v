// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2004 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   reg [2:0] index_a;
   reg [2:0] index_b;

   prover #(4)    p4  (/*AUTOINST*/
		       // Inputs
		       .clk		(clk),
		       .index_a		(index_a),
		       .index_b		(index_b));
   prover #(32)  p32  (/*AUTOINST*/
		       // Inputs
		       .clk		(clk),
		       .index_a		(index_a),
		       .index_b		(index_b));
   prover #(63)  p63  (/*AUTOINST*/
		       // Inputs
		       .clk		(clk),
		       .index_a		(index_a),
		       .index_b		(index_b));
   prover #(64)  p64  (/*AUTOINST*/
		       // Inputs
		       .clk		(clk),
		       .index_a		(index_a),
		       .index_b		(index_b));
   prover #(72)  p72  (/*AUTOINST*/
		       // Inputs
		       .clk		(clk),
		       .index_a		(index_a),
		       .index_b		(index_b));
   prover #(126) p126 (/*AUTOINST*/
		       // Inputs
		       .clk		(clk),
		       .index_a		(index_a),
		       .index_b		(index_b));
   prover #(128) p128 (/*AUTOINST*/
		       // Inputs
		       .clk		(clk),
		       .index_a		(index_a),
		       .index_b		(index_b));

   integer cyc; initial cyc=0;
   initial index_a = 3'b0;
   initial index_b = 3'b0;
   always @* begin
      index_a = cyc[2:0];  if (index_a>3'd4) index_a=3'd4;
      index_b = cyc[5:3];  if (index_b>3'd4) index_b=3'd4;
   end

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc==99) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule


module prover (
   input       clk,
   input [2:0] index_a,
   input [2:0] index_b
   );

   parameter WIDTH = 4;


   reg signed [WIDTH-1:0] as;
   reg signed [WIDTH-1:0] bs;
   wire [WIDTH-1:0] 	  b = bs;

   always @* begin
      casez (index_a)
	 3'd0: as = {(WIDTH){1'd0}}; // 0
	 3'd1: as = {{(WIDTH-1){1'd0}}, 1'b1}; // 1
	 3'd2: as = {1'b0, {(WIDTH-1){1'd0}}}; // 127 or equiv
	 3'd3: as = {(WIDTH){1'd1}}; // -1
	 3'd4: as = {1'b1, {(WIDTH-1){1'd0}}}; // -128 or equiv
	 default: $stop;
      endcase
      casez (index_b)
	 3'd0: bs = {(WIDTH){1'd0}}; // 0
	 3'd1: bs = {{(WIDTH-1){1'd0}}, 1'b1}; // 1
	 3'd2: bs = {1'b0, {(WIDTH-1){1'd0}}}; // 127 or equiv
	 3'd3: bs = {(WIDTH){1'd1}}; // -1
	 3'd4: bs = {1'b1, {(WIDTH-1){1'd0}}}; // -128 or equiv
	 default: $stop;
      endcase
   end

   reg [7:0] results[4:0][4:0];

   wire gt   = as>b;
   wire gts  = as>bs;
   wire gte  = as>=b;
   wire gtes = as>=bs;
   wire lt   = as<b;
   wire lts  = as<bs;
   wire lte  = as<=b;
   wire ltes = as<=bs;

   reg [7:0] exp;
   reg [7:0] got;

   integer   cyc=0;
   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc>2) begin
`ifdef TEST_VERBOSE
	 $write("results[%d][%d] = 8'b%b_%b_%b_%b_%b_%b_%b_%b;\n",
      		index_a, index_b,
      		gt, gts, gte, gtes, lt, lts, lte, ltes);
`endif
	 exp = results[index_a][index_b];
	 got   = {gt, gts, gte, gtes, lt, lts, lte, ltes};
	 if (exp !== got) begin
	    $display("%%Error: bad comparison width=%0d: %d/%d got=%b exp=%b", WIDTH, index_a,index_b,got, exp);
	    $stop;
	 end
      end
   end

   // Result table
   initial begin
      // Indexes: 0, 1, -1, 127, -128
      //                 Gt Gts Gte Gtes Lt Lts Lte Ltes
      results[0][0] = 8'b0_0_1_1_0_0_1_1;
      results[0][1] = 8'b0_0_0_0_1_1_1_1;
      results[0][2] = 8'b0_0_1_1_0_0_1_1;
      results[0][3] = 8'b0_1_0_1_1_0_1_0;
      results[0][4] = 8'b0_1_0_1_1_0_1_0;
      results[1][0] = 8'b1_1_1_1_0_0_0_0;
      results[1][1] = 8'b0_0_1_1_0_0_1_1;
      results[1][2] = 8'b1_1_1_1_0_0_0_0;
      results[1][3] = 8'b0_1_0_1_1_0_1_0;
      results[1][4] = 8'b0_1_0_1_1_0_1_0;
      results[2][0] = 8'b0_0_1_1_0_0_1_1;
      results[2][1] = 8'b0_0_0_0_1_1_1_1;
      results[2][2] = 8'b0_0_1_1_0_0_1_1;
      results[2][3] = 8'b0_1_0_1_1_0_1_0;
      results[2][4] = 8'b0_1_0_1_1_0_1_0;
      results[3][0] = 8'b1_0_1_0_0_1_0_1;
      results[3][1] = 8'b1_0_1_0_0_1_0_1;
      results[3][2] = 8'b1_0_1_0_0_1_0_1;
      results[3][3] = 8'b0_0_1_1_0_0_1_1;
      results[3][4] = 8'b1_1_1_1_0_0_0_0;
      results[4][0] = 8'b1_0_1_0_0_1_0_1;
      results[4][1] = 8'b1_0_1_0_0_1_0_1;
      results[4][2] = 8'b1_0_1_0_0_1_0_1;
      results[4][3] = 8'b0_0_0_0_1_1_1_1;
      results[4][4] = 8'b0_0_1_1_0_0_1_1;
   end

endmodule
