// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t;
   unsupported_ctl_type unsupported_ctl_type();
   bad_assertcontrol_ctl_type bad_assertcontrol_ctl_type();
endmodule

module unsupported_ctl_type;
   initial begin
      $assertcontrol(1);
      $assertcontrol(2);
      $assertcontrol(6);
      $assertcontrol(7);
      $assertcontrol(8);
      $assertcontrol(9);
      $assertcontrol(10);
      $assertcontrol(11);
   end
endmodule

module bad_assertcontrol_ctl_type;
   initial begin
      $assertcontrol(0);
      $assertcontrol(100);
   end
endmodule
