// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

// Exhaustive cases lowered as if/else chains, checked against reference expressions.

// verilator lint_off CASEINCOMPLETE
// verilator lint_off CASEOVERLAP
// verilator lint_off CASEWITHX
// verilator lint_off CASEX

module t (
    input clk
);

  typedef enum logic [1:0] {
    E0,
    E1,
    E2
  } e_t;

  integer cyc = 0;

  wire [1:0] sel_plain = cyc[1:0];
  wire [2:0] s3 = cyc[2:0];
  e_t e;
  assign e = e_t'(cyc[1:0]);

  logic [3:0] y_plain, y_casez, y_casex, y_never, y_inside, y_overlap, y_unique, y_enum, y_incompl;

  always_comb begin
    case (sel_plain)
      2'd0: y_plain = 4'h1;
      2'd1: y_plain = 4'h2;
      2'd2: y_plain = 4'h4;
      2'd3: y_plain = 4'h8;
    endcase
  end

  always_comb begin
    casez (s3)
      3'b1??: y_casez = 4'h1;
      3'b01?: y_casez = 4'h2;
      3'b001: y_casez = 4'h3;
      3'b000: y_casez = 4'h4;
    endcase
  end

  always_comb begin
    casex (s3)
      3'bxx1: y_casex = 4'h1;
      3'bx10: y_casex = 4'h2;
      3'b100: y_casex = 4'h3;
      3'b000: y_casex = 4'h4;
    endcase
  end

  // Items with X never match in a plain case: the last item is unreachable
  always_comb begin
    case (s3[1:0])
      2'b0x: y_never = 4'hf;
      2'd0: y_never = 4'h1;
      2'd1: y_never = 4'h2;
      2'd2: y_never = 4'h3;
      2'd3: y_never = 4'h4;
      2'b1x: y_never = 4'he;
    endcase
  end

  always_comb begin
    case (s3) inside
      3'b1??: y_inside = 4'h1;
      3'b0?1: y_inside = 4'h2;
      3'b0?0: y_inside = 4'h3;
    endcase
  end

  // First match wins; the last item is reached only for values it covers
  always_comb begin
    casez (s3)
      3'b??1: y_overlap = 4'h1;
      3'b1??: y_overlap = 4'h2;
      3'b0?0: y_overlap = 4'h3;
      3'b1?0: y_overlap = 4'h4;
    endcase
  end

  always_comb begin
    unique case (sel_plain)
      2'd3: y_unique = 4'h1;
      2'd2: y_unique = 4'h2;
      2'd1: y_unique = 4'h3;
      2'd0: y_unique = 4'h4;
    endcase
  end

  // Covers every enum value but not every bit pattern: value 3 matches no item
  always_comb begin
    y_enum = 4'h0;
    unique0 case (e)
      E0: y_enum = 4'h1;
      E1: y_enum = 4'h2;
      E2: y_enum = 4'h3;
    endcase
  end

  always_comb begin
    y_incompl = 4'h0;
    case (sel_plain)
      2'd0: y_incompl = 4'h1;
      2'd1: y_incompl = 4'h2;
      2'd2: y_incompl = 4'h3;
    endcase
  end

  always @(posedge clk) begin
`ifdef TEST_VERBOSE
    $write("[%0t] cyc=%0d s3=%b %h %h %h %h %h %h %h %h %h\n", $time, cyc, s3, y_plain, y_casez,
           y_casex, y_never, y_inside, y_overlap, y_unique, y_enum, y_incompl);
`endif
    `checkd(y_plain, 4'h1 << sel_plain);
    `checkd(y_casez, (s3[2] ? 4'h1 : s3[1] ? 4'h2 : s3[0] ? 4'h3 : 4'h4));
    `checkd(y_casex, (s3[0] ? 4'h1 : s3[1] ? 4'h2 : s3[2] ? 4'h3 : 4'h4));
    `checkd(y_never, 4'(s3[1:0]) + 4'h1);
    `checkd(y_inside, (s3[2] ? 4'h1 : s3[0] ? 4'h2 : 4'h3));
    `checkd(y_overlap, (s3[0] ? 4'h1 : s3[2] ? 4'h2 : 4'h3));
    `checkd(y_unique, 4'h4 - 4'(sel_plain));
    `checkd(y_enum, (sel_plain == 2'd3 ? 4'h0 : 4'(sel_plain) + 4'h1));
    `checkd(y_incompl, (sel_plain == 2'd3 ? 4'h0 : 4'(sel_plain) + 4'h1));
    cyc <= cyc + 1;
    if (cyc == 20) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
