// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// sub instantiates sub2; both are inlined by default.
module sub2 (
    input logic [6:0] p2_in,
    output logic [6:0] p2_out
);
  assign p2_out = p2_in ^ 7'h15;
endmodule

module sub (
    input logic [6:0] sub_in,
    output logic [6:0] sub_out
);
  sub2 u_sub2 (
      .p2_in(sub_in),
      .p2_out(sub_out)
  );
endmodule

// port_out is a pure alias of port_in once inlined, unlike sub/sub2's XOR.
module subpass (
    input logic [6:0] port_in,
    output logic [6:0] port_out
);
  assign port_out = port_in;
endmodule

// 'rst' is a top-level input with no driver in the design, read only by cf_portop and
// set by a VPI put at time 0; the flops also reset from 'init' on the first clock edge.
module t #(
    parameter int INTF_QTY = 3
) (
    input logic rst,
    output logic [6:0] observe = 7'h0
);

  logic clk = 1'b0;
  always #5 clk = ~clk;

  logic [7:0] cyc = 8'h0;
  logic init;
  assign init = cyc == 8'h0;
  always @(posedge clk) begin
    cyc <= cyc + 8'h1;
    if (cyc == 8'd12) begin
      t_vpi_dump_values();
      $write("*-* All Finished *-*\n");
      #1 $finish;
    end
  end

  import "DPI-C" context function void t_vpi_dump_values();
  import "DPI-C" context function void t_vpi_dump_skip(input string name);
  import "DPI-C" context function void t_vpi_dump_cb(input string name);
  import "DPI-C" context function void t_vpi_dump_put(
    input string name,
    input string value
  );
  import "DPI-C" context function void t_vpi_dump_put_rw(
    input string name,
    input string value,
    input string flag = ""
  );

  // Multiply-driven signals resolve by how the model was optimised, so are not dumped
  initial begin
    t_vpi_dump_skip("t.cf_mixfull");
    t_vpi_dump_skip("t.cf_ovl");
    t_vpi_dump_cb("t.cmb1");
    t_vpi_dump_cb("t.cyc");
    t_vpi_dump_put("t.rst", "0");
    t_vpi_dump_values();
  end
  always @(negedge clk) t_vpi_dump_values();
  always @(cyc) begin
    case (cyc)
      8'd7: begin
        t_vpi_dump_put_rw("t.cf_nopre", "52");
        t_vpi_dump_put_rw("t.wo_signed", "2a");
      end
      8'd8: t_vpi_dump_put_rw("t.dead", "2a");
      8'd9: t_vpi_dump_put_rw("t.keep", "20");
      8'd10: t_vpi_dump_put_rw("t.pinned_rw", "69");
      default: ;
    endcase
  end

  typedef struct packed {
    logic [3:0] hi;
    logic [3:0] lo;
  } ps_t;

  // Boundary registers
  logic [6:0] keep = 7'h0;
  logic signed [6:0] skeep = 7'sh0;
  logic [69:0] wkeep = 70'h0;  // >64 bits
  logic [6:0] result = 7'h0;

  logic [6:0] cmb1;
  logic [6:0] cmb2;
  logic [6:0] cmb3;
  assign cmb1 = keep + 7'h7;
  assign cmb2 = cmb1 ^ 7'h2a;
  assign cmb3 = cmb2 + 7'h5;

  logic signed [6:0] scmb;
  assign scmb = skeep - 7'sd3;

  logic [69:0] wcmb;  // >64 bits
  assign wcmb = wkeep + 70'd1;

  // Bit/part select, conditional and >>> operators
  logic bsel;
  assign bsel = keep[2];

  logic [6:0] mux0;
  assign mux0 = keep[0] ? cmb1 : cmb2;

  logic [6:0] psel;
  assign psel = {mux0[3:0], keep[6:4]};

  logic signed [6:0] sshift;
  assign sshift = skeep >>> 2;

  logic [69:0] wsel;  // select-from-wide
  assign wsel = {wkeep[66:0], wkeep[69:67]};

  logic [6:0] alias1;  // aliases
  logic [6:0] alias2;
  assign alias1 = keep;
  assign alias2 = alias1;

  logic [6:0] sub_out;
  sub u_sub (
      .sub_in(keep),
      .sub_out(sub_out)
  );

  // port_out/port_in are true aliases of keep
  logic [6:0] pass_out;
  subpass u_subpass (
      .port_in(keep),
      .port_out(pass_out)
  );

  // Explicit public_flat_rw pragma vs an ordinary combinational net. pinned_rw's driver
  // changes on the negedge, so a put to it is overwritten before the next value dump.
  logic [6:0] nkeep = 7'h0;
  always @(negedge clk) nkeep <= keep;
  logic [6:0] pinned_rw  /* verilator public_flat_rw */;
  assign pinned_rw = nkeep ^ 7'h5;
  logic [6:0] plain_ro;
  assign plain_ro = keep + 7'h1;

  // Combinational always_comb blocks
  logic [6:0] pcomb;
  always_comb pcomb = keep ^ result;

  logic [6:0] cf_uncond;
  always_comb cf_uncond = keep ^ 7'h11;

  logic [6:0] cf_ifelse;
  always_comb begin
    if (keep[0]) cf_ifelse = keep + 7'h1;
    else cf_ifelse = keep - 7'h1;
  end

  logic [6:0] cf_ifdef;
  always_comb begin
    cf_ifdef = keep + 7'h4;
    if (keep[1]) cf_ifdef = ~keep;
  end

  logic [6:0] cf_readsrecon;
  always_comb cf_readsrecon = cmb1 ^ 7'h2;

  logic [6:0] cf_readscomb;
  always_comb cf_readscomb = cf_uncond + 7'h3;

  logic [6:0] cf_case;
  always_comb begin
    case (keep[1:0])
      2'd0: cf_case = keep;
      2'd1: cf_case = keep + 7'h1;
      2'd2: cf_case = keep + 7'h2;
      default: cf_case = keep + 7'h3;
    endcase
  end

  logic [6:0] cf_partial;
  always_comb begin
    cf_partial = 7'h0;
    cf_partial[3:0] = keep[3:0];
  end

  logic [7:0] cf_vlsb;
  always_comb begin
    cf_vlsb = {keep, 1'b0};
    cf_vlsb[keep[1:0]*2+:2] = skeep[1:0];
  end

  logic [6:0] cf_casepart;
  always_comb begin
    cf_casepart = keep;
    case (keep[1:0])
      2'd0: cf_casepart = keep + 7'h1;
      2'd1: cf_casepart[3:0] = skeep[3:0];
      default: cf_casepart = ~keep;
    endcase
  end

  logic [6:0] cf_mta;
  logic [6:0] cf_mtb;
  always_comb begin
    cf_mta = keep + 7'h6;
    cf_mtb = cf_mta ^ 7'h1;
  end

  // Multi-range partial assembly
  logic [7:0] cf_ctv;
  assign cf_ctv[3:0] = keep[3:0];
  assign cf_ctv[7:4] = skeep[3:0];

  ps_t cf_cts;
  assign cf_cts.hi = keep[3:0];
  assign cf_cts.lo = skeep[3:0];

  // Full assign then a partial overwrite, and two overlapping partial assigns
  /* verilator lint_off MULTIDRIVEN */
  wire [6:0] cf_mixfull;
  assign cf_mixfull = keep;
  assign cf_mixfull[2:0] = skeep[2:0];

  wire [6:0] cf_ovl;
  assign cf_ovl[4:0] = keep[4:0];
  assign cf_ovl[6:2] = skeep[4:0];
  /* verilator lint_on MULTIDRIVEN */

  // Partial assignment leaving high bits undriven
  /* verilator lint_off LATCH */
  logic [6:0] cf_nopre;
  always_comb begin
    cf_nopre[3:0] = keep[3:0];
  end

  // Genuine latch
  logic [6:0] cf_latch;
  always_comb begin
    if (keep[2]) cf_latch = keep;
  end
  /* verilator lint_on LATCH */

  logic [6:0] cf_selfread;  // self-read target
  always_comb begin
    cf_selfread = keep;
    cf_selfread = cf_selfread + 7'h1;
  end

  logic [6:0] cf_portop;  // port-read candidate
  assign cf_portop = rst ? 7'h0 : keep;

  // Write-only registers
  logic [6:0] dead = 7'h0;
  logic [6:0] wo_plain = 7'h0;
  logic signed [6:0] wo_signed = 7'sh0;
  logic [69:0] wo_wide = 70'h0;

  // Flop with a single downstream reader (via 'observe')
  logic [6:0] cmb3_reg = 7'h0;

  always_ff @(posedge clk) begin
    if (init) begin
      keep <= 7'h0;
      skeep <= 7'sh0;
      wkeep <= 70'h0;
      result <= 7'h0;
      cmb3_reg <= 7'h0;
      dead <= 7'h0;
      wo_plain <= 7'h0;
      wo_signed <= 7'sh0;
      wo_wide <= 70'h0;
      observe <= 7'h0;
    end
    else begin
      keep <= keep + 7'h3;
      skeep <= skeep - 7'sd2;
      wkeep <= wkeep + 70'd5;
      result <= cmb3;
      cmb3_reg <= cmb3;
      dead <= keep + 7'h9;
      wo_plain <= keep + 7'h9;
      wo_signed <= skeep - 7'sd1;
      wo_wide <= wkeep + 70'd11;
      observe <= result ^ cmb3_reg ^ alias2 ^ sub_out ^ pass_out ^ pinned_rw ^ plain_ro
               ^ pcomb ^ cf_uncond ^ cf_ifelse
               ^ cf_ifdef ^ cf_readsrecon ^ cf_readscomb ^ cf_case
               ^ cf_partial ^ cf_vlsb[6:0] ^ cf_casepart ^ cf_mta ^ cf_mtb
               ^ cf_nopre ^ cf_latch ^ cf_selfread
               ^ cf_ctv[6:0] ^ {cf_cts[6:0]};
    end
  end

endmodule
