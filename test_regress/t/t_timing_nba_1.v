// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2022 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

module t;
  integer cyc = 0;

  reg [7:0] a;
  reg [127:0] b;

  always #1 begin
    cyc <= cyc + 1;
    if (cyc == 0) begin
      a <= 8'hFF;
      a[7] <= 1'b0;
    end
    else if (cyc == 1) begin
`ifdef TEST_VERBOSE
      $write("a = %x\n", a);
`endif
      if (a != 8'h7F) $stop;
    end
    else if (cyc == 2) begin
      b <= 128'hFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF;
      b[127] <= 1'b0;
    end
    else if (cyc == 3) begin
`ifdef TEST_VERBOSE
      $write("b = %x\n", b);
`endif
      if (b != 128'h7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF) $stop;
    end
    else if (cyc > 3) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  // NBAs to a whole unpacked array update it: after a delay, in a fork, and in a clocked
  // process. An NBA to a single element updates it too.
  logic clk = 0;
  logic [7:0] arr[0:3];
  logic [7:0] arr_fork[0:3];
  logic [7:0] arr_clk[0:3];
  logic [7:0] arr_elem[0:3];
  logic [7:0] arr_src[0:3] = '{8'h11, 8'h22, 8'h33, 8'h44};
  initial #1 arr <= arr_src;
  initial
  fork
    #1 arr_fork <= arr_src;
  join_none
  initial #1 clk = 1;
  always @(posedge clk) begin
    arr_clk <= arr_src;
    arr_elem[1] <= arr_src[1];
  end
  initial begin
    #2;
    foreach (arr_src[i]) begin
      if (arr[i] !== arr_src[i] || arr_fork[i] !== arr_src[i] || arr_clk[i] !== arr_src[i]) $stop;
    end
    if (arr_elem[1] !== 8'h22) $stop;
  end

endmodule
