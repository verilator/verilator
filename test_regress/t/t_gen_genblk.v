// DESCRIPTION: Verilator: Verilog Test module
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define CONCAT(a,b) a``b
`define SHOW_LINED `CONCAT(show, `__LINE__)

bit fails;

module t (/*AUTOARG*/
   // Inputs
   clk, reset_l
   );

   input        clk;
   input        reset_l;

   generate
      begin : direct_ignored
         show #(`__LINE__) show1();

         if (1) begin check #(`__LINE__, 1) show2(); end
      end

      begin : empty_DISAGREE
         // DISAGREEMENT: if empty unnamed begin/end counts
         begin end

         if (1) begin check #(`__LINE__, 0) show2(); end
      end

      begin : empty_named_DISAGREE
         // DISAGREEMENT: if empty named begin/end counts
         begin : empty_inside_named end

         if (1) begin check #(`__LINE__, 0) show2(); end
      end

      begin : unnamed_counts
         // DISAGREEMENT: if unnamed begin/end counts
         begin
            show #(`__LINE__) show1();
         end

         if (1) begin check #(`__LINE__, 0) show2(); end
      end

      begin : named_counts
         // DISAGREEMENT: if named begin/end counts
         begin : named
            show #(`__LINE__) show1();
         end

         if (1) begin check #(`__LINE__, 0) show2(); end
      end

      begin : if_direct_counts
         if (0) ;
         else if (0) ;
         else if (1) show #(`__LINE__) show1();

         if (1) begin check #(`__LINE__, 2) show2(); end
      end

      begin : if_begin_counts
         if (0) begin end
         else if (0) begin show #(`__LINE__) show1_NOT(); end
         else if (1) begin show #(`__LINE__) show1(); end

         if (1) begin check #(`__LINE__, 2) show2(); end
      end

      begin : if_named_counts
         if (1) begin : named
            show #(`__LINE__) show1();
            if (1) begin : subnamed
               show #(`__LINE__) show1s();
            end
         end

         if (1) begin check #(`__LINE__, 2) show2(); end
      end

      begin : begin_if_counts
         begin
            if (0) begin end
            else if (0) begin show #(`__LINE__) show1_NOT(); end
            else if (1) begin show #(`__LINE__) show1(); end
         end
         // DISAGREEMENT: this could be genblk01
         if (1) begin check #(`__LINE__, 2) show2(); end
      end

      begin : for_empty_counts
         // DISAGREEMENT: if empty genfor counts
         for (genvar g = 0; g < 1; ++g) ;

         if (1) begin check #(`__LINE__, 0) show2(); end
      end

      begin : for_direct_counts
         for (genvar g = 0; g < 1; ++g)
            show #(`__LINE__) show1();

         if (1) begin check #(`__LINE__, 2) show2(); end
      end

      begin : for_named_counts
         for (genvar g = 0; g < 1; ++g) begin : fornamed
            show #(`__LINE__) show1();
         end

         if (1) begin check #(`__LINE__, 2) show2(); end
      end

      begin : for_begin_counts
         for (genvar g = 0; g < 1; ++g) begin
            show #(`__LINE__) show1();
         end

         if (1) begin check #(`__LINE__, 2) show2(); end
      end

      begin : if_if
         if (0) ;
         else if (0) begin : namedb
         end
         else begin
            if (0) begin end
            else if (1) begin
               show #(`__LINE__) show1();
            end
         end

         if (1) begin check #(`__LINE__, 2) show2(); end
      end

      begin : case_direct
         case (1)
           0 : show #(`__LINE__) show1a_NOT();
           1 : show #(`__LINE__) show1();
           2 : show #(`__LINE__) show1c_NOT();
         endcase

         if (1) begin check #(`__LINE__, 2) show2(); end
      end

      begin : case_begin_counts
         case (1)
           0 : begin show #(`__LINE__) show1a_NOT(); end
           1 : begin show #(`__LINE__) show1(); end
           2 : begin show #(`__LINE__) show1c_NOT(); end
         endcase

         if (1) begin check #(`__LINE__, 2) show2(); end
      end

      begin : case_named_counts
         case (1)
           0 : begin : subnamed show #(`__LINE__) show1a_NOT(); end
           1 : begin : subnamed show #(`__LINE__) show1(); end
           2 : begin : subnamed show #(`__LINE__) show1c_NOT(); end
         endcase

         if (1) begin check #(`__LINE__, 2) show2(); end
      end

   endgenerate

   int cyc;

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 999) begin
         if (fails) $stop;
         else $write("*-* All Finished *-*\n");
         $finish;
      end

   end
endmodule

module show #(parameter LINE=0) ();
   // Each instance compares on unique cycle based on line number
   // so we get deterministic ordering (versus using an initial)
   always @ (posedge t.clk) begin
      if (t.cyc == LINE) begin
         $display("%03d: got=%m", LINE);
      end
   end
endmodule

module check #(parameter LINE=0, parameter EXP=0) ();
   string mod;
   int    gennum;
   int    pos;

   always @ (posedge t.clk) begin
      if (t.cyc == LINE) begin
         mod = $sformatf("%m");

         gennum = 0;
         for (int pos = 0; pos < mod.len(); ++pos) begin
            if (mod.substr(pos, pos+5) == "genblk") begin
               pos += 6;
               // verilator lint_off WIDTH
               gennum = mod[pos] - "0";
               // verilator lint_on WIDTH
               break;
            end
         end

         $write("%03d: got=%s exp=%0d gennum=%0d ", LINE, mod, EXP, gennum);
         if (EXP == 0) $display(" <ignored>");
         else if (gennum != EXP) begin
            $display (" %%Error");
            fails = 1;
         end
         else $display;

         $display;
      end
   end
endmodule
