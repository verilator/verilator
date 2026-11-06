// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module sub #(
    parameter int N = 1
) (
    input clk,
    input int cyc
);
  /*verilator no_inline_module*/
  for (genvar i = 0; i < N; ++i) begin : gen
    string s;
    always @(posedge clk) begin
      s <= $sformatf("%0d", cyc * (i + 1));
      if (cyc == 5) `checks(s, $sformatf("%0d", 4 * (i + 1)));
    end
  end
endmodule

module t (
    input clk
);
  int cyc = 0;
  string q[$];
  string pub  /*verilator public_flat_rw*/;

  // Explicitly constructed members nested 3, 2, 1 and 0 levels deep with --comp-limit-members 3
  sub #(.N(20)) u_20 (.*);
  sub #(.N(5)) u_5 (.*);
  sub #(.N(3)) u_3 (.*);
  // Exact square and cube boundaries of the member limit.
  sub #(.N(9)) u_9 (.*);
  sub #(.N(27)) u_27 (.*);

  for (genvar i = 0; i < 40; ++i) begin : gen
    string s;
    always @(posedge clk) begin
      s <= $sformatf("%0d", cyc + i);
      if (cyc == 5) `checks(s, $sformatf("%0d", 4 + i));
    end
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    q.push_back(gen[39].s);
    pub <= gen[7].s;
    if (cyc == 6) begin
      `checks(q[5], "43");
      `checks(pub, "11");
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
