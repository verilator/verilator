// DESCRIPTION: Verilator: Get agregate type parameter from array of interfaces
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

package scp;
  typedef struct packed {
    int unsigned Capacity;
    int unsigned LineSize;
  } cfg_t;
endpackage

interface sct_if #(
  parameter scp::cfg_t cfg = 0
)();

  localparam int  SC_NUM_LINES = cfg.Capacity / cfg.LineSize;

  typedef logic [(cfg.Capacity / cfg.LineSize)-1:0] sc_num_lines_t;

  typedef logic [SC_NUM_LINES-1:0] sc_num_lines_2_t;

endinterface

interface sc_if #(
  parameter scp::cfg_t cfg = 0
)();
  sct_if #(cfg) types();

endinterface

module sc #(parameter scp::cfg_t cfg=0) (
  sc_if io
);

  localparam int  SC_NUM_LINES = io.types.SC_NUM_LINES;

  typedef io.types.sc_num_lines_t sc_num_lines_t;
  typedef io.types.sc_num_lines_2_t sc_num_lines_2_t;

  initial begin
    #1;
    $display("SC_NUM_LINES = %d", SC_NUM_LINES);
    $display("bits SC_NUM_LINES = %d", $bits(sc_num_lines_t));
    $display("bits SC_NUM_LINES_2 = %d", $bits(sc_num_lines_2_t));
    `checkd(SC_NUM_LINES, 16);
    `checkd($bits(sc_num_lines_t), 16);
    `checkd($bits(sc_num_lines_2_t), 16);
  end
endmodule

module t();

  localparam scp::cfg_t sc_cfg = '{
    Capacity : 1024,
    LineSize : 64
  };

  sc_if #(sc_cfg) sc_io ();

  sc #(sc_cfg) simple_cache(
    .io(sc_io)
  );

  initial begin
    #2;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
