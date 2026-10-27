// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class Cls;
  localparam int TABLE[64] = '{
      100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115,
      116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131,
      132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147,
      148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163
  };
  static function int get(int i);
    return TABLE[i];
  endfunction
endclass

module t;
  logic clk = 0;
  always #5 clk = ~clk;

  int cyc = 0;
  always @(posedge clk) begin
    cyc <= cyc + 1;
    `checkd(Cls::get(cyc), 100 + cyc);
    if (cyc == 63) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
