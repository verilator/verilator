// DESCRIPTION: Verilator: Verify function calls through generate-case block references
//
// When a function is defined inside a generate-case item and called via a
// dotted reference (e.g. blk.f()), the FUNCREF must survive generate
// pruning.  Previously the FUNCREF could point to a function in a pruned
// case item, causing a broken-link internal error.
//
// A case item holding only a generate if is directly nested (IEEE 1800-2023
// 27.5), so its blocks are named 'blk' in the module scope, not under a
// 'genblk' scope.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Hongseok Choi
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module sub #(
    parameter int P = 1
) (
    output int o
);
  // Referenced before the blocks are declared
  assign o = blk.f(P);

  generate
    case (P)
      1, 2:
      if (P == 1) begin : blk
        int w = 1;
        function automatic int f(input int i);
          f = i + 10;
        endfunction
      end
      else begin : blk
        int w = 2;
        function automatic int f(input int i);
          f = i + 20;
        endfunction
      end
      4: begin : blk
        int w = 4;
        function automatic int f(input int i);
          f = i + 40;
        endfunction
      end
      default:
      begin : blk
        int w = 7;
        function automatic int f(input int i);
          f = i + 70;
        endfunction
      end
    endcase
  endgenerate
endmodule

module t;
  int o1;
  int o2;
  int o4;
  int o7;

  sub #(.P(1)) u1 (.o(o1));
  sub #(.P(2)) u2 (.o(o2));
  sub #(.P(4)) u4 (.o(o4));
  sub #(.P(7)) u7 (.o(o7));

  initial begin
    #1;
    `checkd(o1, 11);
    `checkd(o2, 22);
    `checkd(o4, 44);
    `checkd(o7, 77);
    `checkd(u1.blk.w, 1);
    `checkd(u2.blk.w, 2);
    `checkd(u4.blk.w, 4);
    `checkd(u7.blk.w, 7);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
