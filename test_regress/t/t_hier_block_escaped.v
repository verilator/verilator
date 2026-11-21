// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

// Escaped top module name
module \t$top (
    input clk
);

  int cyc = 0;
  logic [6:0] a;
  logic [6:0] b;
  logic [6:0] comb;
  logic [6:0] seq;
  logic [6:0] kw;

  assign a = cyc[6:0];
  assign b = cyc[6:0] ^ 7'h5a;

  // Escaped module and instance names
  \sub.esc \u.sub (
      .\clk.in (clk),
      .\input (a),
      .\$dollar (b),
      .\unique (7'd3),
      .\out.comb+1 (comb),
      .\1seq[out] (seq)
  );

  // Port named with a common C++ word
  \sub.vlt u_cpp_word (
      clk,
      a,
      kw
  );

  always @(posedge clk) begin
    cyc <= cyc + 1;
    `checkd(comb, a + b + 7'd3);
    if (cyc > 0) `checkd(seq, a - 7'd1);
    if (cyc > 0) `checkd(kw, a - 7'd1);
    if (cyc == 10) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule

// Escaped port names that are not legal simple identifiers
module \sub.esc (
    input \clk.in ,
    input logic [6:0] \input ,
    input logic [6:0] \$dollar ,
    input logic [6:0] \unique ,
    output logic [6:0] \out.comb+1 ,
    output logic [6:0] \1seq[out]
);  /*verilator hier_block*/
  assign \out.comb+1 = \input + \$dollar + \unique ;
  // Escaped hierarchical block inside another
  \leaf"esc \u.leaf (
      .\clk.in (\clk.in ),
      .\d.in (\input ),
      .\q.out (\1seq[out] )
  );
endmodule

module \leaf"esc (
    input \clk.in ,
    input logic [6:0] \d.in ,
    output logic [6:0] \q.out
);  /*verilator hier_block*/
  always_ff @(posedge \clk.in ) \q.out <= \d.in ;
endmodule

// Hierarchical block set by t_hier_block_escaped.vlt
// verilator lint_off SYMRSVDWORD
module \sub.vlt (
    input clk,
    input logic [6:0] interrupt,
    output logic [6:0] o
);
  always_ff @(posedge clk) o <= interrupt;
endmodule
