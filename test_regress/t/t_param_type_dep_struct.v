// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Packed struct type param with dependent field widths.  $bits and
// field access on a typed-by-paramtype variable must see the correct
// per-spec field widths.  Also exercises the #7445 CVA6 pattern
// (struct member access on a VARREF of a parameterized type).

module m #(
    parameter int  W = 8,
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
  m #(.W(4))  i4  ();
  m #(.W(8))  i8  ();
  m #(.W(16)) i16 ();

  initial begin
    #1;
    if ($bits(i4.t_sig) !== 8)   begin $write("%%Error i4.t_sig bits\n");   $stop; end
    if ($bits(i4.t_sig.a) !== 4) begin $write("%%Error i4.t_sig.a bits\n"); $stop; end
    if ($bits(i4.t_sig.b) !== 4) begin $write("%%Error i4.t_sig.b bits\n"); $stop; end
    if ($bits(i4.a_sig) !== 4)   begin $write("%%Error i4.a_sig bits\n");   $stop; end
    if (i4.t_sig.a !== 4'hF) begin $write("%%Error i4.t_sig.a=%h\n", i4.t_sig.a); $stop; end
    if (i4.t_sig.b !== 4'hF) begin $write("%%Error i4.t_sig.b=%h\n", i4.t_sig.b); $stop; end
    if (i4.a_sig !== 4'hF)   begin $write("%%Error i4.a_sig=%h\n", i4.a_sig);     $stop; end

    if ($bits(i8.t_sig) !== 16)  begin $write("%%Error i8.t_sig bits\n");   $stop; end
    if ($bits(i8.t_sig.a) !== 8) begin $write("%%Error i8.t_sig.a bits\n"); $stop; end
    if ($bits(i8.t_sig.b) !== 8) begin $write("%%Error i8.t_sig.b bits\n"); $stop; end
    if ($bits(i8.a_sig) !== 8)   begin $write("%%Error i8.a_sig bits\n");   $stop; end
    if (i8.t_sig.a !== 8'hFF) begin $write("%%Error i8.t_sig.a=%h\n", i8.t_sig.a); $stop; end
    if (i8.t_sig.b !== 8'hFF) begin $write("%%Error i8.t_sig.b=%h\n", i8.t_sig.b); $stop; end
    if (i8.a_sig !== 8'hFF)   begin $write("%%Error i8.a_sig=%h\n", i8.a_sig);     $stop; end

    if ($bits(i16.t_sig) !== 32)   begin $write("%%Error i16.t_sig bits\n");   $stop; end
    if ($bits(i16.t_sig.a) !== 16) begin $write("%%Error i16.t_sig.a bits\n"); $stop; end
    if ($bits(i16.t_sig.b) !== 16) begin $write("%%Error i16.t_sig.b bits\n"); $stop; end
    if ($bits(i16.a_sig) !== 16)   begin $write("%%Error i16.a_sig bits\n");   $stop; end
    if (i16.t_sig.a !== 16'hFFFF) begin $write("%%Error i16.t_sig.a=%h\n", i16.t_sig.a); $stop; end
    if (i16.t_sig.b !== 16'hFFFF) begin $write("%%Error i16.t_sig.b=%h\n", i16.t_sig.b); $stop; end
    if (i16.a_sig !== 16'hFFFF)   begin $write("%%Error i16.a_sig=%h\n", i16.a_sig);     $stop; end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
