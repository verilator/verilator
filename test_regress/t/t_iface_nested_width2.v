// DESCRIPTION: Verilator: Localparam with package function call using interface param
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

package utils;
  function automatic int f_bits (int val);
    return (val <= 1) ? 1 : $clog2(val);
  endfunction
endpackage

package aerial;
  // Configuration structure
  typedef struct packed {
    // CB Configuration
    int unsigned CBRids;
    int unsigned CBPids;
    int unsigned CBFnum;
    // Coarse parameters
    int unsigned NumAitile;
    int unsigned NumCca;
    // CCA Parameters
    int unsigned NumCc;
    // CC Parameters
    int unsigned CCNumWaves;
    int unsigned CCNumWaveThreads;
    int unsigned CCNumIds;  // check this one
  } cfg_t;
endpackage

package cb;
  typedef struct packed {
    int unsigned Rids;         // ring id assigned to port
    int unsigned Pids;         // packet id
    int unsigned Fnum;         // flit number
    int unsigned XdatSize;     // raw packet data size
  } cfg_t;
endpackage

package cca;
   typedef logic [11:0] csr_index_t;
   typedef logic [1:0] cmd_bnum_t;
   typedef logic [3:0] rq_cmd_t;
   typedef logic [3:0] rs_cmd_t;
   typedef union packed {
      rq_cmd_t rq;
      rs_cmd_t rs;
   } cmd_t;
endpackage: cca

interface aicc_types_if #(parameter aerial::cfg_t cfg=0)();
  //
  typedef logic [$clog2(cfg.NumCc)-1:0] cc_index_t;
  typedef logic [$clog2(cfg.CCNumIds)-1:0] trans_id_t;

  typedef struct packed {
    logic hdr_vld;
    logic [1:0] bnum;
    logic is_rq;
    cca::cmd_t cmd;
    cc_index_t cc_index;
    trans_id_t trans_id;
  } cmd_meta_t;

  typedef union packed {
    logic [cfg.CCNumWaveThreads*64-1:0] raw;
    logic [cfg.CCNumWaveThreads-1:0][63:0] raw_a;
  } cmd_data_t;

  typedef struct packed {
    cmd_meta_t meta;
    cmd_data_t d;
  } cmd_beat_t;
endinterface

interface cb_port_vc_if #(parameter cb::cfg_t cfg=0)();

  typedef logic [$clog2(cfg.Rids)-1:0] rid_t;
  typedef logic [$clog2(cfg.Pids)-1:0] pid_t;
  typedef logic [$clog2(cfg.Fnum)-1:0] fnum_t;
  typedef logic [cfg.XdatSize-1:0] xdat_t;

  typedef struct packed {
    xdat_t dat;
    fnum_t fnum;
    logic first;
    logic last;
    rid_t dest_rid;
  } tx_beat_t;

  tx_beat_t tx_beat;
endinterface

module simple_macro_mem #(
  parameter int p_num_buffered_rq = 16,
  parameter int p_storage_size = 65536
 )(
  aicc_types_if aicc_types,
  // CB Interface
  cb_port_vc_if cb_vc0_io,
  cb_port_vc_if cb_vc1_io
 );

  typedef aicc_types.cmd_beat_t cmd_beat_t;

  logic flit_ot_vld_d, flit_ot_vld_q;
  cmd_beat_t flit_ot_d, flit_ot_q;

  always_comb begin
    cb_vc1_io.tx_beat = 'b0;

    if(flit_ot_vld_q) begin
      cb_vc1_io.tx_beat.dat = flit_ot_q;
    end
  end
endmodule

module tm_top #(
  parameter aerial::cfg_t aer_cfg=0)(
    // Interface to SMM from CB
    cb_port_vc_if cb_vc0_io,
    cb_port_vc_if cb_vc1_io
  );

  aicc_types_if #(aer_cfg) aicc_types();

  simple_macro_mem #() simple_macro_mem(
    .aicc_types(aicc_types),
    .cb_vc0_io(cb_vc0_io),
    .cb_vc1_io(cb_vc1_io)
  );
endmodule

module aitile_top #(
  parameter aerial::cfg_t aer_cfg=0
)(
 );

  aicc_types_if #(aer_cfg) aicc_types();
  typedef aicc_types.cmd_beat_t cmd_beat_t;

  // cluster bus
  localparam cb::cfg_t cb_cfg = '{
    Rids : aer_cfg.CBRids
    ,Pids : aer_cfg.CBPids
    ,Fnum : aer_cfg.CBFnum
    ,XdatSize:$bits(cmd_beat_t)
  };

  // CB <-> TM (simple macro mem)
  cb_port_vc_if#(cb_cfg) cb_tm_vc0_io();
  cb_port_vc_if#(cb_cfg) cb_tm_vc1_io();

  // TM
  tm_top #(
    .aer_cfg(aer_cfg)
  ) tm_top(
    .cb_vc0_io(cb_tm_vc0_io),
    .cb_vc1_io(cb_tm_vc1_io)
  );

endmodule

module aerial_top #(parameter aerial::cfg_t aer_cfg=0)(

 );

  genvar a;
  localparam int p_num_aitile = aer_cfg.NumAitile;

  aicc_types_if #(aer_cfg) aicc_types();
  typedef aicc_types.cmd_beat_t cmd_beat_t;

  // CB and RBUS
  localparam cb::cfg_t cb_cfg = '{
    Rids : aer_cfg.CBRids
    ,Pids : aer_cfg.CBPids
    ,Fnum : aer_cfg.CBFnum
    ,XdatSize:$bits(cmd_beat_t)
  };

  // cb interfaces (HTM dead ends)
  cb_port_vc_if#(cb_cfg) cb_vc0_io();
  cb_port_vc_if#(cb_cfg) cb_vc1_io();

  // HTM
  tm_top #(
    .aer_cfg(aer_cfg)
  ) tm_top(
    .cb_vc0_io(cb_vc0_io),
    .cb_vc1_io(cb_vc1_io)
  );

  generate
    for(a=0; a<p_num_aitile; a++) begin : gen_aitiles
      aitile_top #(
        .aer_cfg(aer_cfg)
      ) aitile(
      );
    end
  endgenerate

endmodule

module t();

  parameter aerial::cfg_t aer_cfg = '{
    // Cluster Bus
    CBRids : 16
    ,CBPids : 32
    ,CBFnum : 4
    // Coarse parameters
    ,NumAitile : 4
    ,NumCca : 1
    // CCA Parameters
    ,NumCc : 3
    // CC Parameters
    ,CCNumWaves : 4
    ,CCNumWaveThreads : 8
    ,CCNumIds : 5
  };

  aerial_top #(
    .aer_cfg(aer_cfg)
  ) aerial_top();

  // Check that cb_cfg.XdatSize is correctly computed as $bits(cmd_beat_t) = 525
  // for both aerial_top and aitile_top paths
  initial begin
    `checkd(aerial_top.cb_cfg.XdatSize, 525);
    `checkd(aerial_top.gen_aitiles[0].aitile.cb_cfg.XdatSize, 525);
    `checkd(aerial_top.gen_aitiles[1].aitile.cb_cfg.XdatSize, 525);
    `checkd(aerial_top.gen_aitiles[2].aitile.cb_cfg.XdatSize, 525);
    `checkd(aerial_top.gen_aitiles[3].aitile.cb_cfg.XdatSize, 525);
    $display("PASS: All cb_cfg.XdatSize = 525");
  end
endmodule
