// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0
//
//     Simplified version of config struct to pass params to module
//     hierarchy.  This is a more compact version of the previous
//     example used to debug alongside the interface typedef examples.
//

package a_pkg;
endpackage

package cb;
  typedef struct packed {
    int unsigned XdatSize;     // raw packet data size
  } cfg_t;
endpackage

module a_mod();
  typedef struct packed {
    logic hdr_vld;
  } cmd_meta_t;

  typedef struct packed {
    cmd_meta_t meta;
  } cmd_beat_t;

  typedef logic [3:0] cc_index_t;

  localparam cb::cfg_t cb_cfg = '{
    XdatSize:$bits(cmd_beat_t)
  };
endmodule

module top();
  a_mod a_mod_inst();

  initial begin
    #1;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
