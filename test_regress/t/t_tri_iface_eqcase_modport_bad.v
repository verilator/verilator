// DESCRIPTION: Verilator: Verilog Test module
//
// Verify that modport access control is not relaxed by tristate __en
// auto-insertion: accessing a tri signal not exposed through the modport
// should still produce a linker error.
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

interface ifc;
   logic we;
   tri [7:0] d;
   modport no_d_mp (input we);  // d is NOT exposed
endinterface

module chk_bad (
   ifc.no_d_mp io_ifc,
   output logic is_z
);
   assign is_z = (io_ifc.d === 8'hzz);
endmodule

module t;
   ifc i ();
   logic is_z;
   chk_bad u (.io_ifc(i), .is_z(is_z));
   initial $finish;
endmodule
