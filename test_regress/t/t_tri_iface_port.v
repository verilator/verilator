// DESCRIPTION: Verilator: Interface inout port driven locally and externally
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

interface zest_if_local (
    inout [0:0] U27
);
  assign U27[0] = 1'b1;
endinterface

interface zest_if_ext (
    inout [0:0] U28
);
endinterface

module ext_drv (
    zest_if_ext zif,
    input drive_en
);
  assign zif.U28[0] = drive_en ? 1'b1 : 1'bz;
endmodule

interface zest_if_ext_mp (
    inout [0:0] U29
);
  modport drv(inout U29);
endinterface

module ext_drv_mp (
    zest_if_ext_mp.drv zif,
    input drive_en
);
  assign zif.U29[0] = drive_en ? 1'b0 : 1'bz;
endmodule

module t (
    inout [0:0] bus_local,
    inout [0:0] bus_ext,
    inout [0:0] bus_ext_mp,
    input drive_en
);
  zest_if_local zif_local (
      .U27(bus_local)
  );

  zest_if_ext zif_ext (
      .U28(bus_ext)
  );
  ext_drv u_ext_drv (
      .zif(zif_ext),
      .drive_en(drive_en)
  );

  zest_if_ext_mp zif_ext_mp (
      .U29(bus_ext_mp)
  );
  ext_drv_mp u_ext_drv_mp (
      .zif(zif_ext_mp),
      .drive_en(drive_en)
  );
endmodule
