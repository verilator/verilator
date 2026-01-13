// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;

  reg [63:0] sum;  // Checked not in objects
  reg [2:1][4:3] array[5:6][7:8];
  bit [3:2][2:1] array2[5:4][2];
  string did;

  initial begin
    sum = 0;
    foreach (array[]) begin  // NOP
      ++sum;
    end
    `checkh(sum, 0);

    sum = 0;
    foreach (array[,,]) begin  // NOP
      ++sum;
    end
    `checkh(sum, 0);

    foreach (array2[i, j,, l]) begin
      did = {did, $sformatf("; %0d,%0d,,%0d", i, j, l)};
    end
    `checks(did, "; 5,0,,2; 5,0,,1; 5,1,,2; 5,1,,1; 4,0,,2; 4,0,,1; 4,1,,2; 4,1,,1");
    $finish;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
