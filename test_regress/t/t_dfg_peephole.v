// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Geza Lore.
// SPDX-License-Identifier: CC0-1.0

`define STRINGIFY(x) `"x`"

`define signal(name, expr) wire [$bits(expr)-1:0] dfg_``name = expr;


module t (/*AUTOARG*/
   // Outputs
   dfg_SWAP_CONST_IN_COMMUTATIVE_BINARY,
   dfg_SWAP_NOT_IN_COMMUTATIVE_BINARY,
   dfg_SWAP_VAR_IN_COMMUTATIVE_BINARY,
   dfg_PUSH_BITWISE_OP_THROUGH_CONCAT,
   dfg_PUSH_BITWISE_OP_THROUGH_CONCAT_2,
   dfg_PUSH_COMPARE_OP_THROUGH_CONCAT, dfg_REMOVE_WIDTH_ONE_REDUCTION,
   dfg_PUSH_REDUCTION_THROUGH_COND_WITH_CONST_BRANCH,
   dfg_REPLACE_REDUCTION_OF_CONST_AND,
   dfg_REPLACE_REDUCTION_OF_CONST_OR,
   dfg_REPLACE_REDUCTION_OF_CONST_XOR, dfg_REPLACE_EXTEND,
   dfg_PUSH_NOT_THROUGH_COND, dfg_REMOVE_NOT_NOT, dfg_REPLACE_NOT_NEQ,
   dfg_REPLACE_NOT_OF_CONST, dfg_REPLACE_AND_OF_NOT_AND_NOT,
   dfg_REPLACE_AND_OF_CONST_AND_CONST, dfg_REPLACE_AND_WITH_ZERO,
   dfg_REMOVE_AND_WITH_ONES, dfg_REPLACE_CONTRADICTORY_AND,
   dfg_REPLACE_OR_OF_NOT_AND_NOT, dfg_REPLACE_OR_OF_NOT_AND_NEQ,
   dfg_REPLACE_OR_OF_CONCAT_ZERO_LHS_AND_CONCAT_RHS_ZERO,
   dfg_REPLACE_OR_OF_CONCAT_LHS_ZERO_AND_CONCAT_ZERO_RHS,
   dfg_REPLACE_OR_OF_CONST_AND_CONST, dfg_REMOVE_OR_WITH_ZERO,
   dfg_REPLACE_OR_WITH_ONES, dfg_REPLACE_TAUTOLOGICAL_OR,
   dfg_REMOVE_SUB_ZERO, dfg_REPLACE_SUB_WITH_NOT,
   dfg_REMOVE_REDUNDANT_ZEXT_ON_RHS_OF_SHIFT,
   dfg_REPLACE_EQ_OF_CONST_AND_CONST, dfg_REMOVE_FULL_WIDTH_SEL,
   dfg_REMOVE_SEL_FROM_RHS_OF_CONCAT,
   dfg_REMOVE_SEL_FROM_LHS_OF_CONCAT, dfg_PUSH_SEL_THROUGH_CONCAT,
   dfg_PUSH_SEL_THROUGH_REPLICATE, dfg_REPLACE_SEL_FROM_CONST,
   dfg_REPLACE_CONCAT_OF_CONSTS,
   dfg_REPLACE_NESTED_CONCAT_OF_CONSTS_ON_RHS,
   dfg_REPLACE_NESTED_CONCAT_OF_CONSTS_ON_LHS,
   dfg_REPLACE_CONCAT_ZERO_AND_SEL_TOP_WITH_SHIFTR,
   dfg_REPLACE_CONCAT_SEL_BOTTOM_AND_ZERO_WITH_SHIFTL,
   dfg_PUSH_CONCAT_THROUGH_NOTS, dfg_REMOVE_CONCAT_OF_ADJOINING_SELS,
   dfg_REPLACE_NESTED_CONCAT_OF_ADJOINING_SELS_ON_LHS,
   dfg_REPLACE_NESTED_CONCAT_OF_ADJOINING_SELS_ON_RHS,
   dfg_REMOVE_COND_WITH_FALSE_CONDITION,
   dfg_REMOVE_COND_WITH_TRUE_CONDITION,
   dfg_SWAP_COND_WITH_NOT_CONDITION, dfg_SWAP_COND_WITH_NEQ_CONDITION,
   dfg_PULL_NOTS_THROUGH_COND, dfg_REPLACE_COND_WITH_THEN_BRANCH_ZERO,
   dfg_REPLACE_COND_WITH_THEN_BRANCH_ONES,
   dfg_REPLACE_COND_WITH_ELSE_BRANCH_ZERO,
   dfg_REPLACE_COND_WITH_ELSE_BRANCH_ONES, dfg_PUSH_SEL_THROUGH_COND,
   dfg_PUSH_SEL_THROUGH_SHIFTL, dfg_REPLACE_SEL_FROM_SEL,
   // Inputs
   clk
   );
   input clk;

   // Sadly verilog-mode cannot look in macros so need to define these
   // separately
   output dfg_SWAP_CONST_IN_COMMUTATIVE_BINARY;
   output dfg_SWAP_NOT_IN_COMMUTATIVE_BINARY;
   output dfg_SWAP_VAR_IN_COMMUTATIVE_BINARY;
   output dfg_PUSH_BITWISE_OP_THROUGH_CONCAT;
   output dfg_PUSH_BITWISE_OP_THROUGH_CONCAT_2;
   output dfg_PUSH_COMPARE_OP_THROUGH_CONCAT;
   output dfg_REMOVE_WIDTH_ONE_REDUCTION;
   output dfg_PUSH_REDUCTION_THROUGH_COND_WITH_CONST_BRANCH;
   output dfg_REPLACE_REDUCTION_OF_CONST_AND;
   output dfg_REPLACE_REDUCTION_OF_CONST_OR;
   output dfg_REPLACE_REDUCTION_OF_CONST_XOR;
   output dfg_REPLACE_EXTEND;
   output dfg_PUSH_NOT_THROUGH_COND;
   output dfg_REMOVE_NOT_NOT;
   output dfg_REPLACE_NOT_NEQ;
   output dfg_REPLACE_NOT_OF_CONST;
   output dfg_REPLACE_AND_OF_NOT_AND_NOT;
   output dfg_REPLACE_AND_OF_CONST_AND_CONST;
   output dfg_REPLACE_AND_WITH_ZERO;
   output dfg_REMOVE_AND_WITH_ONES;
   output dfg_REPLACE_CONTRADICTORY_AND;
   output dfg_REPLACE_OR_OF_NOT_AND_NOT;
   output dfg_REPLACE_OR_OF_NOT_AND_NEQ;
   output dfg_REPLACE_OR_OF_CONCAT_ZERO_LHS_AND_CONCAT_RHS_ZERO;
   output dfg_REPLACE_OR_OF_CONCAT_LHS_ZERO_AND_CONCAT_ZERO_RHS;
   output dfg_REPLACE_OR_OF_CONST_AND_CONST;
   output dfg_REMOVE_OR_WITH_ZERO;
   output dfg_REPLACE_OR_WITH_ONES;
   output dfg_REPLACE_TAUTOLOGICAL_OR;
   output dfg_REMOVE_SUB_ZERO;
   output dfg_REPLACE_SUB_WITH_NOT;
   output dfg_REMOVE_REDUNDANT_ZEXT_ON_RHS_OF_SHIFT;
   output dfg_REPLACE_EQ_OF_CONST_AND_CONST;
   output dfg_REMOVE_FULL_WIDTH_SEL;
   output dfg_REMOVE_SEL_FROM_RHS_OF_CONCAT;
   output dfg_REMOVE_SEL_FROM_LHS_OF_CONCAT;
   output dfg_PUSH_SEL_THROUGH_CONCAT;
   output dfg_PUSH_SEL_THROUGH_REPLICATE;
   output dfg_REPLACE_SEL_FROM_CONST;
   output dfg_REPLACE_CONCAT_OF_CONSTS;
   output dfg_REPLACE_NESTED_CONCAT_OF_CONSTS_ON_RHS;
   output dfg_REPLACE_NESTED_CONCAT_OF_CONSTS_ON_LHS;
   output dfg_REPLACE_CONCAT_ZERO_AND_SEL_TOP_WITH_SHIFTR;
   output dfg_REPLACE_CONCAT_SEL_BOTTOM_AND_ZERO_WITH_SHIFTL;
   output dfg_PUSH_CONCAT_THROUGH_NOTS;
   output dfg_REMOVE_CONCAT_OF_ADJOINING_SELS;
   output dfg_REPLACE_NESTED_CONCAT_OF_ADJOINING_SELS_ON_LHS;
   output dfg_REPLACE_NESTED_CONCAT_OF_ADJOINING_SELS_ON_RHS;
   output dfg_REMOVE_COND_WITH_FALSE_CONDITION;
   output dfg_REMOVE_COND_WITH_TRUE_CONDITION;
   output dfg_SWAP_COND_WITH_NOT_CONDITION;
   output dfg_SWAP_COND_WITH_NEQ_CONDITION;
   output dfg_PULL_NOTS_THROUGH_COND;
   output dfg_REPLACE_COND_WITH_THEN_BRANCH_ZERO;
   output dfg_REPLACE_COND_WITH_THEN_BRANCH_ONES;
   output dfg_REPLACE_COND_WITH_ELSE_BRANCH_ZERO;
   output dfg_REPLACE_COND_WITH_ELSE_BRANCH_ONES;
   output dfg_PUSH_SEL_THROUGH_COND;
   output dfg_PUSH_SEL_THROUGH_SHIFTL;
   output dfg_REPLACE_SEL_FROM_SEL;

   integer cyc = 0;

   reg [63:0] crc = 64'h5aef0c8d_d70a4497;
   reg [63:0] rcr;
   wire       logic [127:0] rcr_crc = {rcr, crc};
   wire       logic [127:0] crc_rep = {2{crc}};
   wire       logic [63:0] const_a;
   wire       logic [63:0] const_b;

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
      rcr <= ~crc;

`ifdef REF
      if (cyc >= 100_000) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
`endif
   end

   // 64'0 but don't tell V3Const
`define ZERO (const_a & ~const_a)
   // 64'1 but don't tell V3Const
`define ONES (const_a | ~const_a)
   // x, but in a way only DFG understands
`define DFG(x) ((|`ONES) ? (x) : (~x))

   `signal(SWAP_CONST_IN_COMMUTATIVE_BINARY, crc + const_a);
   `signal(SWAP_NOT_IN_COMMUTATIVE_BINARY, crc + ~crc);
   `signal(SWAP_VAR_IN_COMMUTATIVE_BINARY, rcr + crc);
   `signal(PUSH_BITWISE_OP_THROUGH_CONCAT, 32'h12345678 ^ {8'h0, crc[23:0]});
   `signal(PUSH_BITWISE_OP_THROUGH_CONCAT_2, 32'h12345678 ^ {rcr[7:0], crc[23:0]});
   `signal(PUSH_COMPARE_OP_THROUGH_CONCAT, 4'b1011 == {2'b10, crc[1:0]});
   `signal(REMOVE_WIDTH_ONE_REDUCTION, &`DFG(crc[0]));
   `signal(PUSH_REDUCTION_THROUGH_COND_WITH_CONST_BRANCH, |(crc[32] ? crc[3:0] : 4'h0));
   `signal(REPLACE_REDUCTION_OF_CONST_AND, &const_a);
   `signal(REPLACE_REDUCTION_OF_CONST_OR,  |const_a);
   `signal(REPLACE_REDUCTION_OF_CONST_XOR, ^const_a);
   `signal(REPLACE_EXTEND, 4'(crc[0]));
   `signal(PUSH_NOT_THROUGH_COND, ~(crc[0] ? crc[4:0] : 5'hb));
   `signal(REMOVE_NOT_NOT, ~`DFG(~`DFG(crc)));
   `signal(REPLACE_NOT_NEQ, ~`DFG(crc != rcr));
   `signal(REPLACE_NOT_OF_CONST, ~4'd0);
   `signal(REPLACE_AND_OF_NOT_AND_NOT, ~crc[0] & ~rcr[0]);
   `signal(REPLACE_AND_OF_CONST_AND_CONST, const_a & const_b);
   `signal(REPLACE_AND_WITH_ZERO, `ZERO & crc);
   `signal(REMOVE_AND_WITH_ONES, `ONES & crc);
   `signal(REPLACE_CONTRADICTORY_AND, crc & ~crc);
   `signal(REPLACE_OR_OF_NOT_AND_NOT, ~crc[0] | ~rcr[0]);
   `signal(REPLACE_OR_OF_NOT_AND_NEQ, ~crc[0] | (rcr != 64'd2));
   `signal(REPLACE_OR_OF_CONCAT_ZERO_LHS_AND_CONCAT_RHS_ZERO, {2'd0, crc[1:0]} | {rcr[1:0], 2'd0});
   `signal(REPLACE_OR_OF_CONCAT_LHS_ZERO_AND_CONCAT_ZERO_RHS, {crc[1:0], 2'd0} | {2'd0, rcr[1:0]});
   `signal(REPLACE_OR_OF_CONST_AND_CONST, const_a | const_b);
   `signal(REMOVE_OR_WITH_ZERO, `ZERO | crc);
   `signal(REPLACE_OR_WITH_ONES, `ONES | crc);
   `signal(REPLACE_TAUTOLOGICAL_OR, crc | ~crc);
   `signal(REMOVE_SUB_ZERO, crc - `ZERO);
   `signal(REPLACE_SUB_WITH_NOT, crc[0] - 1'b1);
   `signal(REMOVE_REDUNDANT_ZEXT_ON_RHS_OF_SHIFT, crc << {2'b0, crc[2:0]});
   `signal(REPLACE_EQ_OF_CONST_AND_CONST, 4'd0 == 4'd1);
   `signal(REMOVE_FULL_WIDTH_SEL, crc[63:0]);
   `signal(REMOVE_SEL_FROM_RHS_OF_CONCAT, rcr_crc[63:0]);
   `signal(REMOVE_SEL_FROM_LHS_OF_CONCAT, rcr_crc[127:64]);
   `signal(PUSH_SEL_THROUGH_CONCAT, rcr_crc[120:0]);
   `signal(PUSH_SEL_THROUGH_REPLICATE, crc_rep[0]);
   `signal(REPLACE_SEL_FROM_CONST, const_a[2]);
   `signal(REPLACE_CONCAT_OF_CONSTS, {const_a, const_b});
   `signal(REPLACE_NESTED_CONCAT_OF_CONSTS_ON_RHS, {`DFG({crc, const_a}), const_b});
   `signal(REPLACE_NESTED_CONCAT_OF_CONSTS_ON_LHS, {const_a, `DFG({const_b, crc})});
   `signal(REPLACE_CONCAT_ZERO_AND_SEL_TOP_WITH_SHIFTR, {62'd0, crc[63:62]});
   `signal(REPLACE_CONCAT_SEL_BOTTOM_AND_ZERO_WITH_SHIFTL, {crc[1:0], 62'd0});
   `signal(PUSH_CONCAT_THROUGH_NOTS, {~crc, ~rcr} );
   `signal(REMOVE_CONCAT_OF_ADJOINING_SELS, {`DFG(crc[10:3]), `DFG(crc[2:1])});
   `signal(REPLACE_NESTED_CONCAT_OF_ADJOINING_SELS_ON_LHS, {crc[10:3], {crc[2:1], rcr}});
   `signal(REPLACE_NESTED_CONCAT_OF_ADJOINING_SELS_ON_RHS, {`DFG({rcr, crc[10:3]}), crc[2:1]});
   `signal(REMOVE_COND_WITH_FALSE_CONDITION, &`ZERO ? crc : rcr);
   `signal(REMOVE_COND_WITH_TRUE_CONDITION, |`ONES ? crc : rcr);
   `signal(SWAP_COND_WITH_NOT_CONDITION, (~crc[0] & |`ONES) ? crc : rcr);
   `signal(SWAP_COND_WITH_NEQ_CONDITION, rcr != crc ? crc : rcr);
   `signal(PULL_NOTS_THROUGH_COND, crc[0] ? ~crc[4:0] : ~rcr[4:0]);
   `signal(REPLACE_COND_WITH_THEN_BRANCH_ZERO, crc[0] ? |`ZERO : crc[1]);
   `signal(REPLACE_COND_WITH_THEN_BRANCH_ONES, crc[0] ? |`ONES : crc[1]);
   `signal(REPLACE_COND_WITH_ELSE_BRANCH_ZERO, crc[0] ? crc[1] : |`ZERO);
   `signal(REPLACE_COND_WITH_ELSE_BRANCH_ONES, crc[0] ? crc[1] : |`ONES);

   assign const_a =  (crc | ~crc) & 64'h0123456789abcdef;
   assign const_b = ~(crc & ~crc) & 64'h98badefc10325647;

   // Some selects need extra temporaries
   wire [63:0] sel_from_cond = crc[0] ? crc : const_a;
   wire [63:0] sel_from_shiftl = crc << 10;
   wire [31:0] sel_from_sel = crc[10+:32];

   `signal(PUSH_SEL_THROUGH_COND, sel_from_cond[2]);
   `signal(PUSH_SEL_THROUGH_SHIFTL, sel_from_shiftl[20:0]);
   `signal(REPLACE_SEL_FROM_SEL, sel_from_sel[4:3]);

   // Sel from not requires the operand to have a sinle sink, so can't use
   // the chekc due to the raw expression referencing the operand
   wire [63:0] sel_from_not_tmp = ~(crc >> rcr[2:0] << crc[3:0]);
   wire        sel_from_not = sel_from_not_tmp[2];
   always @(posedge clk) if ($c(0)) $display(sel_from_not); // Do not remove signal
endmodule
