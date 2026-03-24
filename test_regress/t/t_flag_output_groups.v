// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`ifdef verilator
 `define no_optimize(v) $c(v)
`else
 `define no_optimize(v) (v)
`endif
// verilog_format: on

virtual class Base;
  pure virtual function int get_param;
endclass
class Foo #(
    int N = 17
) extends Base;
  function int get_param;
    return `no_optimize(N);
  endfunction
endclass

module t (
    input clk
);

  localparam MAX = 128;
  Base q[$];
  generate
    // should result in many C++ files
    genvar i;
    for (i = 0; i < MAX; i++)
    initial begin
      automatic Foo #(i) item = new;
      q.push_back(item);
    end
  endgenerate
  always @(posedge clk) begin
    static int sum = 0;
    foreach (q[i]) sum += q[i].get_param();
    if (sum != MAX * (MAX - 1) / 2) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
