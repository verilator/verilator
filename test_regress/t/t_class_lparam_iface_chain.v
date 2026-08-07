// DESCRIPTION: Verilator: Verilog Test module
//
// Interface-instance parameter pins whose value chains through a
// class-scope-resolved localparam (typedef alias of a parameterized
// class, e.g. inst::b). Same cell-deparam fix that handles module
// instances must also handle interface instances and downstream
// port-bound consumers.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

interface SubIface #(
    parameter int IW
) ();
  logic [IW-1:0] data;
endinterface

// Module that takes an interface port - must elaborate after the iface
// cell pin is fully constified.
module Consumer (
    SubIface si
);
endmodule

module t;
  virtual class C #(
      parameter int a
  );
    localparam int b = a;
  endclass

  typedef C#(8) c8;
  typedef C#(13) c13;

  // Deferred lparams
  localparam int b8 = c8::b;
  localparam int b13 = c13::b;
  // Chained
  localparam int b8_alias = b8;

  // Iface pin = bare VarRef to deferred lparam
  SubIface #(b8) i_bare ();
  // Iface pin = chained VarRef
  SubIface #(b8_alias) i_chain ();
  // Iface pin = expression mixing deferred lparams
  SubIface #(b8 + b13) i_expr ();
  // Iface used as a module port - exercises the iface-cell-first path
  Consumer cons (.si(i_bare));

  initial begin
    `checkh(b8, 32'd8);
    `checkh(b13, 32'd13);
    `checkh(b8_alias, 32'd8);
    `checkh($bits(i_bare.data), 32'd8);
    `checkh($bits(i_chain.data), 32'd8);
    `checkh($bits(i_expr.data), 32'd21);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
