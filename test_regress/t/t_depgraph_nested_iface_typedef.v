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

typedef struct packed {
  int unsigned AddrBits;
  int unsigned DataBits;
  int unsigned IdBits;
  int unsigned UserBits;
} axi_cfg_t;

// Innermost interface - like axi4_if.sv in the real design
interface axi4_if #(parameter axi_cfg_t cfg = '{32, 64, 4, 0})();
  typedef logic [cfg.AddrBits-1:0] addr_t;
  typedef logic [cfg.DataBits-1:0] data_t;
  typedef logic [cfg.IdBits-1:0] id_t;
  typedef logic [cfg.UserBits-1:0] user_t;
  typedef logic [cfg.DataBits/8-1:0] strb_t;

  // AXI channel typedef
  typedef struct packed {
    id_t     id;
    addr_t   addr;
    logic [7:0] len;
  } ar_chan_t;

  typedef struct packed {
    id_t     id;
    data_t   data;
    logic [1:0] resp;
    logic    last;
  } r_chan_t;

  ar_chan_t ar;
  r_chan_t  r;
endinterface

// Middle interface - wraps the AXI interface
interface tlb_io_if #(parameter axi_cfg_t axi_cfg = '{32, 64, 4, 0})();
  axi4_if #(.cfg(axi_cfg)) axi_tlb_io();

  // Capture typedef from nested interface
  typedef axi_tlb_io.r_chan_t r_chan_t;
  typedef axi_tlb_io.ar_chan_t ar_chan_t;
endinterface

// Outer interface - contains the middle interface
interface cca_io_if #(parameter axi_cfg_t axi_cfg = '{32, 64, 4, 0})();
  tlb_io_if #(.axi_cfg(axi_cfg)) tlb_io();

  // Capture typedef from doubly-nested interface
  typedef tlb_io.r_chan_t r_chan_t;
  typedef tlb_io.ar_chan_t ar_chan_t;
endinterface

// Module that uses the doubly-nested typedef - this is where the error occurred
module cca_xbar #(parameter axi_cfg_t axi_cfg = '{32, 64, 4, 0})(
  cca_io_if cca_io
);
  // This line was causing "Internal Error: Unlinked" before the fix
  // because cca_io.tlb_io.r_chan_t references a typedef from a nested interface
  typedef cca_io.tlb_io.r_chan_t m_r_chan_t;
  typedef cca_io.tlb_io.ar_chan_t m_ar_chan_t;

  m_r_chan_t r_data;
  m_ar_chan_t ar_data;

  initial begin
    // Verify the typedef resolved correctly - compare against the actual interface signal
    `checkd($bits(m_r_chan_t), $bits(cca_io.tlb_io.axi_tlb_io.r));
    `checkd($bits(m_ar_chan_t), $bits(cca_io.tlb_io.axi_tlb_io.ar));

    // Verify width matches expected formula based on axi_cfg parameter
    // r_chan_t = id(IdBits) + data(DataBits) + resp(2) + last(1)
    // ar_chan_t = id(IdBits) + addr(AddrBits) + len(8)
    `checkd($bits(m_r_chan_t), axi_cfg.IdBits + axi_cfg.DataBits + 2 + 1);
    `checkd($bits(m_ar_chan_t), axi_cfg.IdBits + axi_cfg.AddrBits + 8);
  end
endmodule

module t();
  localparam axi_cfg_t cfg1 = '{AddrBits: 32, DataBits: 64, IdBits: 4, UserBits: 2};
  localparam axi_cfg_t cfg2 = '{AddrBits: 40, DataBits: 128, IdBits: 8, UserBits: 4};

  // Instantiate outer interface
  cca_io_if #(.axi_cfg(cfg1)) cca_io1();
  cca_io_if #(.axi_cfg(cfg2)) cca_io2();

  // Instantiate modules that use doubly-nested typedefs
  cca_xbar #(.axi_cfg(cfg1)) xbar1(.cca_io(cca_io1));
  cca_xbar #(.axi_cfg(cfg2)) xbar2(.cca_io(cca_io2));

  // Also test direct typedef access in top module
  typedef cca_io1.tlb_io.r_chan_t top_r_chan_t;
  typedef cca_io2.tlb_io.ar_chan_t top_ar_chan_t;

  initial begin
    #1;
    // cfg1: DataBits=64, IdBits=4 -> r_chan_t = 4+64+2+1 = 71
    `checkd($bits(top_r_chan_t), 71);
    // cfg2: AddrBits=40, IdBits=8 -> ar_chan_t = 8+40+8 = 56
    `checkd($bits(top_ar_chan_t), 56);

    #1;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
