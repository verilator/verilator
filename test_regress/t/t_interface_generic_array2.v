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
    a[2].v = 'hface;
    a[3].v = 'hcafe;
  end
endmodule

module GenericModule2D (interface a[2][2]);
  initial begin
    #3;
    if (a[0][0].v != 'hdead) $stop;
    a[0][1].v = 'hbeef;
    if (a[1][0].v != 'hface) $stop;
    a[1][1].v = 'hcafe;
  end
endmodule

module GenericModuleRng (interface a[5:3]);
  initial begin
    #5;
    if (a[3].v != 'hdead) $stop;
    if (a[4].v != 'hbeef) $stop;
    a[5].v = 'hface;
  end
endmodule

module t;
  inf inf1d[4]();
  inf inf2d[2][2]();
  inf infrng[5:3]();
  GenericModule1D mod1d(inf1d);
  GenericModule2D mod2d(inf2d);
  GenericModuleRng modrng(infrng);
  initial begin
    inf1d[0].v = 'hdead;
    inf1d[1].v = 'hbeef;
    #2;
    if (inf1d[2].v != 'hface) $stop;
    if (inf1d[3].v != 'hcafe) $stop;
    inf2d[0][0].v = 'hdead;
    inf2d[1][0].v = 'hface;
    #2;
    if (inf2d[0][1].v != 'hbeef) $stop;
    if (inf2d[1][1].v != 'hcafe) $stop;
    infrng[3].v = 'hdead;
    infrng[4].v = 'hbeef;
    #2;
    if (infrng[5].v != 'hface) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
