// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// verilator lint_off MULTIDRIVEN

// ---------------- Compare semantics (=== / !==) ----------------
interface ifc_cmp;
  logic we;
  tri [7:0] d;
endinterface

module drv_cmp (
  ifc_cmp io_ifc
);
  assign io_ifc.d = io_ifc.we ? 8'h5A : 8'hzz;
endmodule

module chk_cmp (
  ifc_cmp io_ifc,
  output logic is_z,
  output logic is_5a,
  output logic not_z,
  output logic not_5a
);
  assign is_z = (io_ifc.d === 8'hzz);
  assign is_5a = (io_ifc.d === 8'h5A);
  assign not_z = (io_ifc.d !== 8'hzz);
  assign not_5a = (io_ifc.d !== 8'h5A);
endmodule

interface ifc_cmp_mp;
  logic we;
  tri [7:0] d;
  modport drv_mp (input we, inout d);
  modport chk_mp (input we, inout d);
endinterface

module drv_cmp_mp (
  ifc_cmp_mp.drv_mp io_ifc
);
  assign io_ifc.d = io_ifc.we ? 8'h5A : 8'hzz;
endmodule

module chk_cmp_mp (
  ifc_cmp_mp.chk_mp io_ifc,
  output logic is_z,
  output logic is_5a,
  output logic not_z,
  output logic not_5a
);
  assign is_z = (io_ifc.d === 8'hzz);
  assign is_5a = (io_ifc.d === 8'h5A);
  assign not_z = (io_ifc.d !== 8'hzz);
  assign not_5a = (io_ifc.d !== 8'h5A);
endmodule

module passthru_cmp (
  ifc_cmp io_ifc
);
  drv_cmp u_drv (.*);
endmodule

// ---------------- Mixed local + external contributors ----------------
interface ifc_mix;
  logic we_local;
  logic we_ext;
  tri [7:0] d;
  assign d = we_local ? 8'hA5 : 8'hzz;
endinterface

module drv_mix (
  ifc_mix io_ifc
);
  assign io_ifc.d = io_ifc.we_ext ? 8'h3C : 8'hzz;
endmodule

interface ifc_mix_mp;
  logic we_local;
  logic we_ext;
  tri [7:0] d;
  modport drv_mp (input we_ext, inout d);
  assign d = we_local ? 8'hA5 : 8'hzz;
endinterface

module drv_mix_mp (
  ifc_mix_mp.drv_mp io_ifc
);
  assign io_ifc.d = io_ifc.we_ext ? 8'h3C : 8'hzz;
endmodule

module t;
  // ---- Compare semantics: basic ----
  ifc_cmp i_cmp ();
  logic is_z, is_5a, not_z, not_5a;
  drv_cmp u_drv_cmp (.io_ifc(i_cmp));
  chk_cmp u_chk_cmp (.io_ifc(i_cmp), .is_z(is_z), .is_5a(is_5a),
                     .not_z(not_z), .not_5a(not_5a));

  // ---- Compare semantics: modport ----
  ifc_cmp_mp i_cmp_mp ();
  logic mp_is_z, mp_is_5a, mp_not_z, mp_not_5a;
  drv_cmp_mp u_drv_cmp_mp (.io_ifc(i_cmp_mp));
  chk_cmp_mp u_chk_cmp_mp (.io_ifc(i_cmp_mp), .is_z(mp_is_z), .is_5a(mp_is_5a),
                           .not_z(mp_not_z), .not_5a(mp_not_5a));

  // ---- Compare semantics: deep hierarchy ----
  ifc_cmp i_cmp_deep ();
  logic deep_is_z, deep_is_5a, deep_not_z, deep_not_5a;
  passthru_cmp u_cmp_deep (.io_ifc(i_cmp_deep));
  chk_cmp u_chk_cmp_deep (.io_ifc(i_cmp_deep), .is_z(deep_is_z), .is_5a(deep_is_5a),
                          .not_z(deep_not_z), .not_5a(deep_not_5a));

  // ---- Mixed contributors ----
  ifc_mix i_mix ();
  drv_mix u_mix (.io_ifc(i_mix));

  ifc_mix_mp i_mix_mp ();
  drv_mix_mp u_mix_mp (.io_ifc(i_mix_mp));

  initial begin
    // ---- Compare semantics ----
    i_cmp.we = 1'b0;
    i_cmp_mp.we = 1'b0;
    i_cmp_deep.we = 1'b0;
    #1;

    `checkh(is_z, 1'b1);
    `checkh(is_5a, 1'b0);
    `checkh(not_z, 1'b0);
    `checkh(not_5a, 1'b1);
    `checkh(mp_is_z, 1'b1);
    `checkh(mp_is_5a, 1'b0);
    `checkh(mp_not_z, 1'b0);
    `checkh(mp_not_5a, 1'b1);
    `checkh(deep_is_z, 1'b1);
    `checkh(deep_is_5a, 1'b0);

    #1;
    i_cmp.we = 1'b1;
    i_cmp_mp.we = 1'b1;
    i_cmp_deep.we = 1'b1;
    #1;

    `checkh(is_z, 1'b0);
    `checkh(is_5a, 1'b1);
    `checkh(not_z, 1'b1);
    `checkh(not_5a, 1'b0);
    `checkh(mp_is_z, 1'b0);
    `checkh(mp_is_5a, 1'b1);
    `checkh(mp_not_z, 1'b1);
    `checkh(mp_not_5a, 1'b0);
    `checkh(deep_is_z, 1'b0);
    `checkh(deep_is_5a, 1'b1);

    #1;
    i_cmp.we = 1'b0;
    i_cmp_mp.we = 1'b0;
    i_cmp_deep.we = 1'b0;
    #1;

    `checkh(is_z, 1'b1);
    `checkh(is_5a, 1'b0);
    `checkh(not_z, 1'b0);
    `checkh(not_5a, 1'b1);
    `checkh(mp_is_z, 1'b1);
    `checkh(mp_is_5a, 1'b0);
    `checkh(mp_not_z, 1'b0);
    `checkh(mp_not_5a, 1'b1);
    `checkh(deep_is_z, 1'b1);
    `checkh(deep_is_5a, 1'b0);

    // ---- Mixed contributors ----
    i_mix.we_local = 1'b0;
    i_mix.we_ext = 1'b0;
    i_mix_mp.we_local = 1'b0;
    i_mix_mp.we_ext = 1'b0;
    #1;

    `checkh(i_mix.d, 8'hzz);
    `checkh(i_mix_mp.d, 8'hzz);

    #1;
    i_mix.we_local = 1'b1;
    i_mix.we_ext = 1'b0;
    i_mix_mp.we_local = 1'b1;
    i_mix_mp.we_ext = 1'b0;
    #1;
    `checkh(i_mix.d, 8'hA5);
    `checkh(i_mix_mp.d, 8'hA5);

    #1;
    i_mix.we_local = 1'b0;
    i_mix.we_ext = 1'b1;
    i_mix_mp.we_local = 1'b0;
    i_mix_mp.we_ext = 1'b1;
    #1;
    `checkh(i_mix.d, 8'h3C);
    `checkh(i_mix_mp.d, 8'h3C);

    #1;
    i_mix.we_local = 1'b1;
    i_mix.we_ext = 1'b1;
    i_mix_mp.we_local = 1'b1;
    i_mix_mp.we_ext = 1'b1;
    #1;
    `checkh(i_mix.d, 8'hBD);
    `checkh(i_mix_mp.d, 8'hBD);

    #1;
    i_mix.we_local = 1'b0;
    i_mix.we_ext = 1'b0;
    i_mix_mp.we_local = 1'b0;
    i_mix_mp.we_ext = 1'b0;
    #1;
    `checkh(i_mix.d, 8'hzz);
    `checkh(i_mix_mp.d, 8'hzz);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
