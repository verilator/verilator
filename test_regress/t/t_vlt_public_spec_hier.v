// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0


module leaf_nested();
  int leaf = 0;
endmodule

module leaf_sib();
  int leaf = 0;
endmodule

module leaf_arr();
  int leaf = 0;
endmodule

module leaf_gen();
  int leaf = 0;
endmodule

module leaf_orphan();
  logic [7:0] orphan;
endmodule

module esc_m();
  int \var.with.dot = 0;
endmodule

module mid_m();
  int mid_tmp = 0;
  leaf_nested i_leaf ();
endmodule

interface ifc();
  logic [7:0] data;
endinterface

module top();
  mid_m i_mid_0 ();
  mid_m i_mid_1 ();

  leaf_sib sub_a ();
  leaf_sib sub_b ();
  leaf_sib sub_c ();
  leaf_sib sub_d ();

  leaf_orphan i_orph_a ();
  leaf_orphan i_orph_b ();

  esc_m \inst.with.dot ();
  esc_m \foo[abc] ();

  leaf_arr i_arr1 [1:0] ();
  leaf_arr i_arr2 [1:0][1:0] ();
  leaf_arr i_narr [0:-2] ();
  leaf_arr \foo] [3:0] ();

  ifc i_single ();
  ifc i_iarr [2:0] ();
  ifc i_md [1:0][1:0] ();

  generate
    for (genvar i = 0; i < 2; ++i) begin : gen_loop
      int loop_local;
      leaf_gen i_sub ();
    end
  endgenerate
  generate
    for (genvar i = -2; i < 0; ++i) begin : gen_neg
      int neg_local;
    end
  endgenerate
  generate
    if (1) begin : gen_if
      int if_local;
      leaf_gen i_sub ();
    end
  endgenerate

  initial begin
    $c("Verilated::scopesDump();");
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
