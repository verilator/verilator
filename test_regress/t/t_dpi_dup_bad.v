// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2009 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module t;

  // Same name w/ different args
  import "DPI-C" dpii_fa_bit = function int oth_f_int1(input int i);
  import "DPI-C" pure dpii_fa_bit = function int oth_f_int2(
    input int i,
    input int bad);

  // Same, but void so the call sits in statement position
  import "DPI-C" dpii_fa_void = function void oth_f_void1(input int i);
  import "DPI-C" dpii_fa_void = function void oth_f_void2(
    input int i,
    input int bad);

  int o1;
  int o2;

  initial begin
    o1 = oth_f_int1(1);
    o2 = oth_f_int2(1, 2);
    oth_f_void1(1);
    oth_f_void2(1, 2);
    $stop;
  end

endmodule
