// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2026 by Wilson Snyder
// SPDX-License-Identifier: CC0-1.0
//

// DESCRIPTION: Verilator: Test nested interface typedef access
// This replicates the pattern from a much larger design that was
// failing with the localparam changes - accessing a typedef from
// a doubly-nested interface
//

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

package cb;
  typedef struct packed {
    logic [31:0] Rids;
    logic [31:0] Pids;
    logic [31:0] Fnum;
    logic [31:0] XdatSize;
  } cfg_t;
endpackage

package a_pkg;
  typedef struct packed {
    int unsigned p_a;
    int unsigned p_b;
  } cfg_t;
endpackage

interface other_types_if #(parameter a_pkg::cfg_t cfg=0)();
  // Create a struct that results in 525 bits
  typedef struct packed {
    logic [cfg.p_a-1:0] field1;
    logic [cfg.p_b-1:0] field2;
  } cmd_beat_t;

endinterface

// Simple interface that takes a parameter
interface simple_if #(parameter cb::cfg_t cfg=0)();
  logic [cfg.Rids-1:0] rids;
  logic [cfg.Pids-1:0] pids;
  logic [cfg.Fnum-1:0] fnum;
  logic [cfg.XdatSize-1:0] xdat;
endinterface

module TestMod;
  localparam a_pkg::cfg_t ot_cfg = '{
    p_a : 8,
    p_b : 4
  };

  other_types_if #(ot_cfg) other_types();

  typedef other_types.cmd_beat_t cmd_beat_t;

  // This pattern assignment should work correctly
  localparam cb::cfg_t cb_cfg = '{
    Rids : 32'h1,
    Pids : 32'h2,
    Fnum : 32'h3,
    XdatSize : $bits(cmd_beat_t)
  };

  // This should trigger the error - cb_cfg is not recognized as constant
  simple_if#(cb_cfg) cb_vc0_io();

  initial begin
    `checkd(cb_cfg.XdatSize, 12);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
