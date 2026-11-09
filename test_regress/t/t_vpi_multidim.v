// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// Call the C++-linkage wrapper of a test function, as $c cannot declare an extern "C" function
`define CPP_CALL(f) $c32(`"[] { extern int f``_cpp(); return f``_cpp(); }()`")
// verilog_format: on

module t (
    input clk
); /*verilator no_inline_module*/

  logic [3:2][5:3] arr_cdata [1:0][2:1]; // 2x3 (6) bit words
  logic [7:6][12:7] arr_sdata [5:4][6:5]; // 2x6 (12) bit words
  logic [11:10][25:11] arr_idata [9:8][10:9]; // 2x15 (30) bit words
  logic [15:14][44:15] arr_qdata [13:12][14:13]; // 2x30 (60) bit words
  logic [19:18][81:19] arr_wdata [17:16][18:17]; // 2x63 (126) bit words
  // verilator lint_off ASCRANGE
  logic [3:2][1:2][1:0] arr_6d [1:0][1:2][3:2]; // 3 unpacked, 3 packed dims, some ascending
  // verilator lint_on ASCRANGE

  int status;

  initial begin
    arr_6d = '{default: '0};
    arr_6d[1][2][3] = 8'hb4;
`ifdef VERILATOR
    status = `CPP_CALL(mon_check);
`else
    status = $mon_check();
`endif
    if (status != 0) begin
      $write("%%Error: t_vpi_multidim.cpp:%0d: C Test failed\n", status);
      $stop;
    end
`ifndef MS
    // Written by mon_check()
    `checkh(arr_6d[0][1][2], 8'h3c);
    `checkh(arr_6d[0][1][3], 8'h00);
    `checkh(arr_6d[0][2][2], 8'h00);
`endif
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule : t
