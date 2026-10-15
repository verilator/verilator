// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

// Port names of at least 128 characters, the length at which identifiers are hashed internally
`define LONG_CLK clock_port_name_that_is_well_over_the_limit_where_verilator_hashes_identifiers_to_keep_generated_cpp_names_and_file_names_reasonably_short
`define LONG_IN data_input_name_that_is_well_over_the_limit_where_verilator_hashes_identifiers_to_keep_generated_cpp_names_and_file_names_reasonably_short
`define LONG_COMB comb_output_name_that_is_well_over_the_limit_where_verilator_hashes_identifiers_to_keep_generated_cpp_names_and_file_names_reasonably_short
`define LONG_SEQ seq_output_name_that_is_well_over_the_limit_where_verilator_hashes_identifiers_to_keep_generated_cpp_names_and_file_names_reasonably_short

module t (
    input clk
);

  int cyc = 0;
  logic [7:0] in;
  logic [7:0] comb;
  logic [7:0] seq;

  assign in = cyc[7:0];

  sub u_sub (
      .`LONG_CLK(clk),
      .`LONG_IN(in),
      .`LONG_COMB(comb),
      .`LONG_SEQ(seq)
  );

  always @(posedge clk) begin
    cyc <= cyc + 1;
    `checkd(comb, in + 8'd1);
    if (cyc > 0) `checkd(seq, in - 8'd1);
    if (cyc == 10) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule

module sub (
    input `LONG_CLK,
    input logic [7:0] `LONG_IN,
    output logic [7:0] `LONG_COMB,
    output logic [7:0] `LONG_SEQ
);  /*verilator hier_block*/
  assign `LONG_COMB = `LONG_IN + 8'd1;
  always_ff @(posedge `LONG_CLK) `LONG_SEQ <= `LONG_IN;
endmodule
