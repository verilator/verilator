// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Parameterized hierarchical blocks must be replaced by their libraries in the final
// compilation (#7009), each by the library built for its parameter values.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);
  // Library models: a0, a1, a2, m0 and the acc instance inside it, s0, and s1
  localparam int LIBRARY_MODELS = 7;
  int cyc = 0;
  longint data[6], out[6];
  longint expected[6] = '{default: 0};
  for (genvar i = 0; i < 6; ++i) begin : stim
    assign data[i] = longint'(cyc * (i + 3) + i * 7);
  end

  // K=3 is shared by two instances with independent state
  acc #(
      .K(3)
  ) a0 (
      .clk,
      .data(data[0]),
      .out(out[0])
  );
  acc #(
      .K(3)
  ) a1 (
      .clk,
      .data(data[1]),
      .out(out[1])
  );
  // The untyped parameter is a signed -1, which must reach the library
  acc #(
      .K(-1)
  ) a2 (
      .clk,
      .data(data[2]),
      .out(out[2])
  );
  // Also the acc instance inside is a library
  mid #(
      .P(5)
  ) m0 (
      .clk,
      .data(data[3]),
      .out(out[3])
  );
  // Strings that the generated child arguments carry
  str_blk #(
      .S("p q,r")
  ) s0 (
      .clk,
      .data(data[4]),
      .out(out[4])
  );
  str_blk #(
      .S("a//b\\c */")
  ) s1 (
      .clk,
      .data(data[5]),
      .out(out[5])
  );

  function automatic longint str_hash(string s);
    str_hash = 0;
    for (int i = 0; i < s.len(); ++i) str_hash = str_hash * 31 + longint'(s[i]);
  endfunction

  always @(posedge clk) begin
    // Each library adds its value and the parameter's width, so a wrong library changes the sum
    expected[0] <= expected[0] + data[0] + 3 + 32;
    expected[1] <= expected[1] + data[1] + 3 + 32;
    expected[2] <= expected[2] + data[2] - 1 + 32;
    expected[3] <= expected[3] + data[3] + 5 + 32;
    expected[4] <= expected[4] + data[4] + str_hash("p q,r");
    expected[5] <= expected[5] + data[5] + str_hash("a//b\\c */");
  end
  always @(negedge clk) begin
    foreach (out[i]) `checkd(out[i], expected[i]);
    cyc <= cyc + 1;
    if (cyc == 60) begin
`ifdef VERILATOR
      // Every block instance is a library model, with its own thread
      `checkd($c32("Verilated::threadContextp()->threadsInModels()"),
              `ROOT_THREADS + LIBRARY_MODELS);
`endif
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule

module acc #(
    parameter K = 0
) (
    input clk,
    input longint data,
    output longint out
);
  /*verilator hier_block*/
  longint state = 0;
  always @(posedge clk) state <= state + data + longint'(K) + longint'($bits(K));
  assign out = state;
endmodule

module mid #(
    parameter P = 0
) (
    input clk,
    input longint data,
    output longint out
);
  /*verilator hier_block*/
  acc #(
      .K(P)
  ) inner (
      .clk,
      .data,
      .out
  );
endmodule

module str_blk #(
    parameter string S = "x"
) (
    input clk,
    input longint data,
    output longint out
);
  /*verilator hier_block*/
  function automatic longint str_hash();
    str_hash = 0;
    for (int i = 0; i < S.len(); ++i) str_hash = str_hash * 31 + longint'(S[i]);
  endfunction
  longint state = 0;
  always @(posedge clk) state <= state + data + str_hash();
  assign out = state;
endmodule
