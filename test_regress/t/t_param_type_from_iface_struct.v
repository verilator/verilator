// DESCRIPTION: Verilator: Test type parameter from interface struct
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// Exercises skipWidthForTemplateStruct in V3Param::cellPinCleanup.
//
// Pattern: nested parameterized interfaces with struct type parameters:
//   1. Parameterized inner interface (inner_if) defines struct typedefs
//   2. Outer interface (outer_if) contains a nested inner_if instance
//   3. A module takes the outer interface as a port and creates typedefs
//      through two levels of nesting: port.inner.req_t
//   4. Those struct typedefs are passed as type parameters to an inner module
//   5. A separate module creates inner_if clones with different configs,
//      ensuring inner_if gets parameterizedTemplate()=true before the
//      type parameter pins are processed

package cfg_pkg;
  typedef struct packed {
    int unsigned IdBits;
    int unsigned DataBits;
  } cfg_t;
endpackage

// Parameterized inner interface with struct typedefs
interface inner_if #(
    parameter cfg_pkg::cfg_t cfg = '0
);
  typedef struct packed {
    logic [cfg.IdBits-1:0] id;
    logic [cfg.DataBits-1:0] data;
  } req_t;
  typedef struct packed {
    logic [cfg.IdBits-1:0] id;
    logic [1:0] resp;
  } resp_t;
  req_t req;
  resp_t resp;
endinterface

// Outer interface containing a nested inner_if
interface outer_if #(
    parameter cfg_pkg::cfg_t cfg = '0
);
  inner_if #(cfg) inner ();
endinterface

// Module with type parameters (consumer of struct typedefs)
module typed_mod #(
    parameter type req_t = logic,
    parameter type resp_t = logic
) (
    input logic clk
);
  req_t r;
  resp_t s;
  assign r = '0;
  assign s = '0;
endmodule

// Wrapper: takes outer_if ports, typedefs through two-level nesting,
// passes as type parameters to typed_mod
module wrap_mod #(
    parameter int NUM = 1
) (
    input logic clk,
    outer_if ports[NUM]
);
  typedef ports[0].inner.req_t local_req_t;
  typedef ports[0].inner.resp_t local_resp_t;
  typed_mod #(
      .req_t(local_req_t),
      .resp_t(local_resp_t)
  ) u_sub (
      .clk(clk)
  );
endmodule

module t;
  logic clk = 0;
  localparam cfg_pkg::cfg_t CFG_A = '{IdBits: 4, DataBits: 32};
  localparam cfg_pkg::cfg_t CFG_B = '{IdBits: 8, DataBits: 64};

  // Force inner_if to be cloned with different configs first
  inner_if #(CFG_A) early_a ();
  inner_if #(CFG_B) early_b ();
  assign early_a.req = '0;
  assign early_a.resp = '0;
  assign early_b.req = '0;
  assign early_b.resp = '0;

  outer_if #(CFG_A) io[2] ();
  wrap_mod #(
      .NUM(2)
  ) u_wrap (
      .clk(clk),
      .ports(io)
  );

  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
