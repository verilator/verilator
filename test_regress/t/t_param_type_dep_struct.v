// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

// Packed struct type param with dependent field widths.  $bits and
// field access on a typed-by-paramtype variable must see the correct
// per-spec field widths.  Also exercises the #7445 CVA6 pattern
// (struct member access on a VARREF of a parameterized type).

module m #(
    parameter int W = 8,
    parameter type T = struct packed {
      logic [W-1:0] a;
      logic [W-1:0] b;
    }
) ();
  T t_sig;
  logic [W-1:0] a_sig;
  initial t_sig = '1;
  initial a_sig = t_sig.a;
endmodule

module t;
  m #(.W(4)) i4 ();
  m #(.W(8)) i8 ();
  m #(.W(16)) i16 ();

  initial begin
    #1;
    `checkh($bits(i4.t_sig), 8);
    `checkh($bits(i4.t_sig.a), 4);
    `checkh($bits(i4.t_sig.b), 4);
    `checkh($bits(i4.a_sig), 4);
    `checkh(i4.t_sig.a, 4'hF);
    `checkh(i4.t_sig.b, 4'hF);
    `checkh(i4.a_sig, 4'hF);

    `checkh($bits(i8.t_sig), 16);
    `checkh($bits(i8.t_sig.a), 8);
    `checkh($bits(i8.t_sig.b), 8);
    `checkh($bits(i8.a_sig), 8);
    `checkh(i8.t_sig.a, 8'hFF);
    `checkh(i8.t_sig.b, 8'hFF);
    `checkh(i8.a_sig, 8'hFF);

    `checkh($bits(i16.t_sig), 32);
    `checkh($bits(i16.t_sig.a), 16);
    `checkh($bits(i16.t_sig.b), 16);
    `checkh($bits(i16.a_sig), 16);
    `checkh(i16.t_sig.a, 16'hFFFF);
    `checkh(i16.t_sig.b, 16'hFFFF);
    `checkh(i16.a_sig, 16'hFFFF);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
