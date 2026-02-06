// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Leela Pakanati
// SPDX-License-Identifier: CC0-1.0

interface iface;
  logic a, b;
  // Dotted path to non-existent signal
  modport mp1(input .in(nonexist.sig));
  // Complex expression not supported as modport expression
  modport mp2(input .in(~a));
endinterface

module t;
  iface intf ();
endmodule
