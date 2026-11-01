// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

class cls;
  task yout(output bit otp);
    otp = 0;
  endtask
  task yref(ref bit otp);
    otp = 0;
  endtask
  task xout(output int otp);
    otp = 0;
  endtask
  task xref(ref int otp);
    otp = 0;
  endtask
endclass

module t (
    input var bit inport
);
  cls c;
  const int cnst = 4;
  initial begin
    c = new;
    // Illegal, IEEE 1800-2023 23.3.3.2, 13.5: cannot write an input variable port
    c.yout(inport);
    c.yref(inport);
    // Illegal, IEEE 1800-2023 6.20.6, 13.5: cannot write a const variable
    c.xout(cnst);
    c.xref(cnst);
  end
endmodule
