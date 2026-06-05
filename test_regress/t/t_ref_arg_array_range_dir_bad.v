// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Unlike packed arrays, unpacked-array element correspondence is range-direction
// dependent, so a 'ref' port of type logic[31:0]$[0:3] must reject an actual of
// type logic[31:0]$[3:0] (see t_ref_arg_array_range_dir for the packed case).

// verilator lint_off ASCRANGE

module t;
  function automatic void fill(ref logic [31:0] arr[0:3]);
    arr[0] = '0;
  endfunction

  logic [31:0] a[3:0];

  initial fill(a);
endmodule
