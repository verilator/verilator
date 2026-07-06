// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2024 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t (
    input logic clk
);
  unsupported_ctl_type unsupported_ctl_type (clk ? 1 : 2);
endmodule

module unsupported_ctl_type (
    input int a
);
  initial begin
    let PassOn = 6;
    let PassOff = 7;
    let FailOn = 8;
    let FailOff = 9;
    let NonvacuousOn = 10;
    let VacuousOff = 11;
    $assertcontrol(PassOn);
    $assertpasson;
    $assertpasson(a);
    $assertpasson(a, t);

    $assertcontrol(PassOff);
    $assertpassoff;
    $assertpassoff(a);
    $assertpassoff(a, t);

    $assertcontrol(FailOn);
    $assertfailon;
    $assertfailon(a);
    $assertfailon(a, t);

    $assertcontrol(FailOff);
    $assertfailoff;
    $assertfailoff(a);
    $assertfailoff(a, t);

    $assertcontrol(NonvacuousOn);
    $assertnonvacuouson;
    $assertnonvacuouson(a);
    $assertnonvacuouson(a, t);

    $assertcontrol(VacuousOff);
    $assertvacuousoff;
    $assertvacuousoff(a);
    $assertvacuousoff(a, t);
  end
endmodule
