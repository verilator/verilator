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

package rial;

// Configuration structure
  typedef struct packed {
    // CCA Parameters
    int unsigned NumDd;
    // CC Parameters
    int unsigned DDNumStuff;
    int unsigned DDNumStuffThreads;
  } cfg_t;
endpackage

package cb;
  typedef struct packed {
    int unsigned XdatSize;     // raw packet data size
  } cfg_t;
endpackage

interface ccia_types_if #(parameter rial::cfg_t cfg=0)();

  // 'base' types
  typedef logic [$clog2(cfg.DDNumStuff)-1:0] wave_index_t;

// types for tb
  typedef struct packed {
    logic [3:0] e_cmd;
    logic en;
    logic csr;
    wave_index_t wave_index;
    logic [11:0] reg_addr;
    logic [64-(4+1+1+$clog2(cfg.DDNumStuff)+12)-1:0] pad0;
  } tl_reg_cmd_t;

  typedef struct packed {
    logic [63:0] raw;
  } tl_addr_cmd_t;

  typedef union packed {
    tl_reg_cmd_t rcmd;
    tl_addr_cmd_t acmd;
  } tl_data_fld_t;

  typedef union packed {
    tl_data_fld_t [cfg.DDNumStuffThreads-1:0] d_a;
  } cmd_data_t;

  typedef struct packed {
    cmd_data_t d;
  } cmd_beat_t;

endinterface

module rial_top #(
  parameter rial::cfg_t aer_cfg=0
)();

// for the types
  ccia_types_if #(aer_cfg) ccia_types();

// genvars and locally defined types
  typedef ccia_types.cmd_beat_t cmd_beat_t;

  // CB and RBUS
  localparam cb::cfg_t cb_cfg = '{
    XdatSize:$bits(cmd_beat_t)
  };

  initial begin
    #1;
    `checkd($bits(ccia_types.tl_data_fld_t), 64);
    `checkd($bits(ccia_types.cmd_data_t), 512);
    `checkd($bits(cmd_beat_t), 512);
    `checkd(cb_cfg.XdatSize, 512);
  end

endmodule

// SOC Top w/IO and SOC configuration
module rial_wrap();

  parameter rial::cfg_t aer_cfg = '{
    NumDd : 3,
    // CC Parameters
    DDNumStuff : 4,
    DDNumStuffThreads : 8
  };

// DUT
  rial_top #(
    .aer_cfg(aer_cfg)
  ) rial_top();

  initial begin
    #2;
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
