// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

interface inf;
  int v;
endinterface

module GenericModule1D (interface a[4]);
  initial begin
    #1;
    if (a[0].v != 'hdead) $stop;
    if (a[1].v != 'hbeef) $stop;
    if (a[2].v != 'hface) $stop;
    if (a[3].v != 'hcafe) $stop;
  end
endmodule

module GenericModule2D (interface a[2][2]);
  initial begin
    #2;
    if (a[0][0].v != 'hdead) $stop;
    if (a[0][1].v != 'hbeef) $stop;
    if (a[1][0].v != 'hface) $stop;
    if (a[1][1].v != 'hcafe) $stop;
  end
endmodule

module t;
  inf inf1d[4]();
  inf inf2d[2][2]();
  GenericModule1D mod1d(inf1d);
  GenericModule2D mod2d(inf2d);
  initial begin
    inf1d[0].v ='hdead;
    inf1d[1].v ='hbeef;
    inf1d[2].v ='hface;
    inf1d[3].v ='hcafe;
    inf2d[0][0].v ='hdead;
    inf2d[0][1].v ='hbeef;
    inf2d[1][0].v ='hface;
    inf2d[1][1].v ='hcafe;
    #3;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
