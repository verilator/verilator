// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2020 Geza Lore
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// verilog_format: off
module t_dpi_result_type_bad;

  // Illegal result types for DPI functions

  // Unpacked structures
  typedef struct { int x; } struct_unpacked;
  import "DPI-C" function struct_unpacked i_struct_unpacked();
  export "DPI-C" function e_struct_unpacked;
  function struct_unpacked e_struct_unpacked(); return '{x: 0}; endfunction
endmodule
