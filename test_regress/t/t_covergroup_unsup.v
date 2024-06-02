// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   int   a;
   int   b;
   logic c;
   int cyc = 0;

   always @(posedge clk) begin
      cyc <= cyc + 1;
   end

   // NOTE this grammar hasn't been checked with other simulators,
   // is here just to avoid uncovered code lines in the grammar.

   covergroup cg_empty;
   endgroup

   covergroup cg_opt;
      type_option.weight = 1;  // cg, cp, cross
      type_option.goal = 99;  // cg, cp, cross
      type_option.comment = "type_option_comment";  // cg, cp, cross
      type_option.strobe = 0;  // cg
      type_option.merge_instances = 1;  // cg
      type_option.distribuge_first = 1;  // cg
      option.name = "the_name";  // cg
      option.weight = 1;  // cg, cp, cross
      option.goal = 98;  // cg, cp, cross
      option.comment = "option_comment";  // cg, cp, cross
      option.at_least = 20;  // cg, cp, cross
      option.auto_bin_max = 10;  // cg, cp
      option.cross_num_print_missing = 2;  // cg, cross
      option.detect_overlap = 1;  // cg, cp
      option.per_instance = 1;  // cg
      option.get_inst_coverage = 1;  // cg
   endgroup

   covergroup cg_clockingevent() @(posedge clk);
   endgroup
   covergroup cg_withfunction() with function sample (a);
   endgroup
   covergroup cg_atat() @@ (begin funca or end funcb);
   endgroup
   covergroup cg_bracket;
      {}
   endgroup
   covergroup cg_bracket;
      { option.name = "option"; }
   endgroup
   covergroup cg_cp;
      coverpoint a;
   endgroup
   covergroup cg_cp_iff;
      coverpoint a iff (b);
   endgroup
   covergroup cg_id_cp_iff;
      id: coverpoint a iff (b);
   endgroup
   covergroup cg_id_cp_id1;
      int id: coverpoint a iff (b);
   endgroup
   covergroup cg_id_cp_id2;
      var int id: coverpoint a iff (b);
   endgroup
   covergroup cg_id_cp_id3;
      var [3:0] id: coverpoint a iff (b);
   endgroup
   covergroup cg_id_cp_id4;
      [3:0] id: coverpoint a iff (b);
   endgroup
   covergroup cg_id_cp_id5;
      signed id: coverpoint a iff (b);
   endgroup

   covergroup cg_cross;
      cross a, b iff (!rst);
   endgroup
   covergroup cg_cross2;
      cross a, b iff (!rst) {}
   endgroup
   covergroup cg_cross3;
      cross a, b { option.comment = "cross"; option.weight = 12; }
   endgroup
   covergroup cg_cross3;
      cross a, b { function void crossfunc; endfunction; }
   endgroup
   covergroup cg_cross_id;
      my_cg_id: cross a, b iff (!rst);
   endgroup

   covergroup cg_binsoroptions_bk1;
      // bins_keyword id/*bin_identifier*/ bins_orBraE '=' '{' open_range_list '}' iffE
      { bins ba = {a}; }
      { bins bar = {a} iff (!rst); }
      { illegal_bins ila = {a}; }
      { ignore_bins iga = {a}; }

      { bins ba[] = {a}; }
      { bins ba[2] = {a}; }

      { bins ba = {a} with { b }; }

      { wildcard bins bwa = {a}; }
      { wildcard bins bwaw = {a} with { b }; }

      { bins def = default; }
      { bins defs = default sequence; }

      { bins bts = ( 1, 2 ); }
      { wildcard bins wbts = ( 1, 2 ); }
      { bins bts2 = ( 2, 3 ), ( [5:6] ) ; }

      { bins bts2 = ( 1,5 => 6,7 ) ; }
      { bins bts2 = ( 3 [*5] ) ; }
      { bins bts2 = ( 3 [*5:6] ) ; }
      { bins bts2 = ( 3 [->5] ) ; }
      { bins bts2 = ( 3 [->5:6] ) ; }
      { bins bts2 = ( 3 [=5] ) ; }
      { bins bts2 = ( 3 [=5:6] ) ; }

   endgroup

   covergroup cg_cross_bins;
      cross a, b {
         bins bin_a = binsof(a);
         bins bin_ai = binsof(a) iff (!rst);
         bins bin_c = binsof(cp.x);
         bins bin_na = ! binsof(a);

         bins bin_d = binsof(a) intersect { b };
         bins bin_nd = ! binsof(a) intersect { b };

         bins bin_e = with (a);
         bins bin_e = ! with (a);

         bins bin_par = (binsof(a));
         bins bin_and = binsof(a) && binsof(b);
         bins bin_or = binsof(a) || binsof(b);
      }
   endgroup

   covergroup cg_more extends cg_empty;
   endgroup

   always @(posedge clk) begin
      if (cyc == 10) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
