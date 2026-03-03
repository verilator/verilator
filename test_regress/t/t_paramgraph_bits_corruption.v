// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//

// DESCRIPTION: Minimal test for sibling interface typedef resolution
// This is the SIMPLEST case that demonstrates the t_lparam_dep_iface10 failure pattern:
// - Two sibling cells of the same interface type with DIFFERENT parameters
// - A module that accesses typedefs from BOTH siblings
//

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

package TestPkg;
  // Create a struct that results in 525 bits like in aerial_wrap
  typedef struct packed {
    logic [31:0] field1;
    logic [31:0] field2;
    logic [31:0] field3;
    logic [31:0] field4;
    logic [31:0] field5;
    logic [31:0] field6;
    logic [31:0] field7;
    logic [31:0] field8;
    logic [31:0] field9;
    logic [31:0] field10;
    logic [31:0] field11;
    logic [31:0] field12;
    logic [31:0] field13;
    logic [31:0] field14;
    logic [31:0] field15;
    logic [31:0] field16;
    logic [12:0]  field17;  // 525 bits total (16*32 + 13)
  } cmd_beat_t;

  typedef struct packed {
    logic [31:0] Rids;
    logic [31:0] Pids;
    logic [31:0] Fnum;
    logic [31:0] XdatSize;  // 32-bit field
  } cfg_t;

  // This pattern assignment should trigger the error
  // The issue is that $bits(cmd_beat_t) evaluation during DepGraph causes corruption
  // where the pattern literal gets a 128-bit constant instead of proper 32-bit assignment
  // Note: cmd_beat_t is referenced directly, not through a localparam type alias
  localparam cfg_t cb_cfg = '{
    Rids : 32'h1,
    Pids : 32'h2,
    Fnum : 32'h3,
    XdatSize : $bits(cmd_beat_t)  // Should be 525, but gets corrupted
  };
endpackage

module TestMod;
  import TestPkg::*;

  initial begin
    $display("XdatSize = %d", cb_cfg.XdatSize);
    `checkd(cb_cfg.XdatSize, 525);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
