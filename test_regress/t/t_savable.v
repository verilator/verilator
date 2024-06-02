// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2012 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk, model
   );
   /*verilator no_inline_module*/   // So we'll get hiearachy we can test
   input clk;

   // Parameter so we can test for different model error
   parameter MODEL_WIDTH = 10;
   input [MODEL_WIDTH-1:0] model;

   initial $write("Model width = %0d\n", MODEL_WIDTH);

   sub sub (/*AUTOINST*/
            // Inputs
            .clk                        (clk));
endmodule

module sub (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   /*verilator no_inline_module*/   // So we'll get hiearachy we can test

   integer      cyc = 0;

   reg [127:0]  save128;
   reg [47:0]   save48;
   reg [1:0]    save2;
   reg [255:0]  cycdone;  // Make sure each cycle executes exactly once
   reg [31:0]   vec[2:1][2:1];
   reg [2:1][2:1][31:0] pvec;
   real         r;
   string       s,s2;
   string       sarr[2:1];
   string       assoc[string];

   string       si;

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d\n", $time, cyc);
`endif
      si = "siimmed";
      cyc <= cyc + 1;
      if (cycdone[cyc[7:0]]) $stop;
      cycdone[cyc[7:0]] <= '1;
      if (cyc==0) begin
         // Setup
         save128 <= 128'hc77bb9b3784ea0914afe43fb79d7b71e;
         save48 <= 48'h4afe43fb79d7;
         save2 <= 2'b10;
         vec[1][1] <= 32'h0101;
         vec[1][2] <= 32'h0102;
         vec[2][1] <= 32'h0201;
         vec[2][2] <= 32'h0202;
         pvec[1][1] <= 32'h10101;
         pvec[1][2] <= 32'h10102;
         pvec[2][1] <= 32'h10201;
         pvec[2][2] <= 32'h10202;
         r <= 1.234;
         s <= "hello";
         sarr[1] <= "sarr[1]";
         sarr[2] <= "sarr[2]";
         assoc["mapped"] <= "Is mapped";
      end
      if (cyc==1) begin
         if ($test$plusargs("save_restore")!=0) begin
            // Don't allow the restored model to run from time 0, it must run from a restore
            $write("%%Error: didn't really restore\n");
            $stop;
         end
      end
      else if (cyc==99) begin
         if (save128 !== 128'hc77bb9b3784ea0914afe43fb79d7b71e) $stop;
         if (save48 !== 48'h4afe43fb79d7) $stop;
         if (save2 !== 2'b10) $stop;
         if (cycdone !== {{(256-99){1'b0}}, {99{1'b1}}}) $stop;
         if (vec[1][1] !== 32'h0101) $stop;
         if (vec[1][2] !== 32'h0102) $stop;
         if (vec[2][1] !== 32'h0201) $stop;
         if (vec[2][2] !== 32'h0202) $stop;
         if (pvec[1][1] !== 32'h10101) $stop;
         if (pvec[1][2] !== 32'h10102) $stop;
         if (pvec[2][1] !== 32'h10201) $stop;
         if (pvec[2][2] !== 32'h10202) $stop;
         if (r != 1.234) $stop;
         $display("%s",s);
         $display("%s",sarr[1]);
         $display("%s",sarr[2]);
         if (assoc["mapped"] != "Is mapped") $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
