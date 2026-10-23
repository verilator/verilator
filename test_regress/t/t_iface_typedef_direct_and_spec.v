// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0
//
// Dimension queries of a type reached through an interface that has both a
// direct (no override) and a specialized instance must fold to a constant. A
// module used as is is never replaced by a specialization, so its types are
// final and the query must not be deferred.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

interface ifc #(
    parameter int N = 1
) ();
  typedef logic [N-1:0] d_t;
endinterface

interface sub_if #(
    parameter int N = 1
) ();
  typedef logic [N-1:0] t_t;
endinterface

interface parent_if #(
    parameter int N = 1
) ();
  typedef logic [N-1:0] d_t;
  sub_if #(.N(N)) s ();
endinterface

module sub #(
    parameter int W = 0,
    parameter int E = 0
) ();
  initial `checkd(W, E);
endmodule

// The type is reached through an interface instance that is used as is, while
// another instance of the same interface is specialized elsewhere.
module direct_user ();
  ifc i ();
  typedef i.d_t local_t;
  localparam int BITS = $bits(local_t);
  sub #(.W(BITS), .E(1)) i_sub ();
endmodule

// The type is reached through a generic interface port, whose spec comes from
// the connection, including a nested sub-interface taking the parent's parameter.
module port_user #(
    parameter int EW = 0,
    parameter int ES = 0
) (
    parent_if p
);
  localparam int BITS = $bits(p.d_t);
  localparam int SUB_BITS = $bits(p.s.t_t);
  localparam int HIGH = $high(p.d_t);
  initial begin
    `checkd(BITS, EW);
    `checkd(SUB_BITS, ES);
    `checkd(HIGH, EW - 1);
  end
endmodule

module t;
  direct_user u_direct ();

  // Direct and specialized instances of one interface side by side.
  ifc i1 ();
  ifc #(.N(5)) i2 ();
  typedef i1.d_t t1;
  typedef i2.d_t t2;
  localparam int W1 = $bits(t1);
  localparam int W2 = $bits(t2);
  localparam int H2 = $high(t2);
  sub #(.W(W1), .E(1)) u_direct_inst ();
  sub #(.W(W2), .E(5)) u_spec_inst ();
  sub #(.W(H2 + 1), .E(5)) u_spec_high ();

  parent_if as_is ();
  parent_if #(.N(5)) specialized ();
  port_user #(.EW(1), .ES(1)) u_port_as_is (.p(as_is));
  port_user #(.EW(5), .ES(5)) u_port_spec (.p(specialized));

  initial begin
    #1;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
