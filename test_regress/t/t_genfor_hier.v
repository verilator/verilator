// DESCRIPTION: Verilator: Demonstrate deferred linking across module
// bondaries
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2015 Todd Strader
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module m1 ();
  logic v1;
endmodule

module m2 #(
    parameter int P = 0
) ();
endmodule

interface i1 #(
    parameter int P = 0
) ();
endinterface

module t;
  for (genvar the_genvar = 0; the_genvar < 4; the_genvar++) begin : m1_b
    m1 m1_inst ();
  end
  for (genvar the_other_genvar = 0; the_other_genvar < 4; the_other_genvar++) begin
    always_comb m1_b[the_other_genvar].m1_inst.v1 = 1'b0;
  end

  // Test: Parameter of a generate block of a loop
  for (genvar i = 0; i < 3; i++) begin : gen_param
    localparam int TWICE = i * 2;
  end

  // Test: Parameters below a generate block of a loop
  for (genvar i = 0; i < 3; i++) begin : gen_below
    i1 #(.P(i + 10)) i1_inst ();
    for (genvar j = 0; j < 2; j++) begin : gen_nested
      localparam int SUM = i * 100 + j;
      m2 #(.P(i * 10 + j)) m2_inst ();
    end
  end

  initial begin
    `checkd(gen_param[0].TWICE, 0);
    `checkd(gen_param[2].TWICE, 4);

    `checkd(gen_below[1].i1_inst.P, 11);
    `checkd(gen_below[2].i1_inst.P, 12);
    `checkd(gen_below[0].gen_nested[1].SUM, 1);
    `checkd(gen_below[2].gen_nested[1].SUM, 201);
    `checkd(gen_below[0].gen_nested[1].m2_inst.P, 1);
    `checkd(gen_below[2].gen_nested[1].m2_inst.P, 21);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
