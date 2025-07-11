// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module sub(input [1:0] i);
endmodule

module t;
  sub s1(1);
  sub s2(1);
  sub s3(1);
  sub s4(1);
  sub s5(1);
  initial begin
      // these should fail
      s1.i = 2;
      force s1.i = '1;

      s2.i = 2;
      release s2.i;

      force s3.i = '1;
      assign s3.i = 2;

      // these should not
      force s4.i = '1;

      release s5.i;
  end
endmodule
