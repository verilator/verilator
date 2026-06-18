// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// verilator lint_off MULTIDRIVEN

interface ifc;
  wire [1:0] w;
  // Self-contained interface-internal tristate driver: 'z while en==0, so any
  // external driver must win the net resolution.
  bit en = 0;
  logic [1:0] wint;
  assign wint = 2'b11;
  assign w = en ? wint : 2'bzz;
  // Read the resolved net from inside the interface (a consumer's view), so the
  // check sees the true resolution, not the driving module's own local copy.
  function automatic logic [1:0] get_w();
    return w;
  endfunction
endinterface

// Interface net made tristate only by an external 'z driver (no internal driver).
interface ifc_tri;
  tri [1:0] w;
endinterface

module driver (
    ifc io,
    input logic [1:0] din
);
  // Plain (non-Z) cross-hierarchy driver of an interface tristate net.
  // This module's own tristate graph has no 'z on io.w, so before the fix this
  // contribution was silently dropped and io.w resolved to the interface-internal
  // 'z (== 0) only.
  assign io.w = din;
endmodule

module driver_tri (
    ifc_tri io,
    input logic [1:0] din
);
  assign io.w = din;
endmodule

module zdriver (
    ifc_tri io
);
  assign io.w = 2'bzz;
endmodule

module t;
  // u_a, u_b: interface nets driven plainly from the top module (depth-0 xref).
  // u_c:      interface net driven plainly from a child module (depth-1 xref).
  ifc u_a ();
  ifc u_b ();
  ifc u_c ();
  // u_e: net is tristate only via zdriver's external 'z; the plain driver must
  // still win (the interface itself has no internal driver).
  ifc_tri u_e ();

  logic [1:0] va, vb, vc, ve;
  assign va = 2'b01;
  assign vb = 2'b10;
  assign vc = 2'b11;
  assign ve = 2'b01;

  assign u_a.w = va;  // plain top-level driver
  assign u_b.w = vb;  // plain top-level driver
  driver u_drv (
      .io(u_c),
      .din(vc)
  );  // plain driver in a child module
  driver_tri u_pdrv (
      .io(u_e),
      .din(ve)
  );  // plain driver of an externally-tristated net
  zdriver u_zdrv (.io(u_e));  // external 'z driver

  initial begin
    #1;
    // The plain external driver must win over the interface-internal 'z.
    `checkh(u_a.get_w(), 2'b01);
    `checkh(u_b.get_w(), 2'b10);
    `checkh(u_c.get_w(), 2'b11);
    // The plain driver must win over an external-only 'z (no internal driver).
    `checkh(u_e.w, 2'b01);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
