// DESCRIPTION: Verilator: Regression for prelim ASCRANGE on cfg-based interface typedefs
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

package axis;
  typedef struct packed {
    int unsigned DataWidth;
  } cfg_t;
endpackage

interface axis_if #(parameter axis::cfg_t cfg = '0)();
  typedef logic [cfg.DataWidth-1:0] tdata_t;
endinterface

module axis_chan #(
  parameter axis::cfg_t chan_cfg = '0
) ();
  axis_if #(chan_cfg) axis_channel_io();
  typedef axis_channel_io.tdata_t data_t;
  localparam int kWidth = $bits(data_t);
  initial begin
    #1;
    `checkd(kWidth,32);
  end
endmodule

module t;
  localparam axis::cfg_t axis_chan_cfg = '{DataWidth: 32};
  axis_chan #(.chan_cfg(axis_chan_cfg)) u_chan();
  initial begin
    #2;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
