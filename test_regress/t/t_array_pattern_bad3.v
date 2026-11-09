// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2018 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// bug1364

module t (
    input clk,
    input res
);

  localparam int N = 2;
  int arr[3];
  initial begin
    arr = '{
        default: '0,  //
        1: '0,  //
        1: '1
    };  // Bad
    arr = '{'0, '1, '0, '1};  // Bad, too many
    arr = '{'0, '1};  // Bad, too few
    begin
      int a2[2];
      arr = '{a2, '0, '1};  // Bad, an array is not an element
      arr = '{0: a2, 1: '0, 2: '1};  // Bad, an array is not an element
    end
    begin
      // Arrays as members, which need {...} instead (see t_array_pattern_concat)
      logic [31:0] base_addrs[3];
      logic [31:0] extra[2];
      logic [31:0] desc[2:0];
      logic [31:0] all_addrs[4];
      logic [31:0] mid[5];
      logic [31:0] multi[5];
      logic [31:0] with_desc[4];
      logic [31:0] dflt[3];
      logic [31:0] with_dflt[4];
      all_addrs = '{base_addrs[0:1], 32'h80003000, 32'h80004000};  // Bad
      mid = '{32'hFF, base_addrs[0:1], 32'hAA, 32'hBB};  // Bad
      multi = '{base_addrs, extra};  // Bad
      with_desc = '{desc[1:0], 32'hAA, 32'hBB};  // Bad
      dflt = '{default: 32'hDD};
      with_dflt = '{dflt, 32'hEE};  // Bad
      all_addrs = '{base_addrs[0:N-1], 32'hAA, 32'hBB};  // Bad
    end
  end

endmodule
