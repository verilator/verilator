// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2009 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

   function int int123(); int123 = 32'h123; endfunction

   function bit         f_bit     ; input bit      i;  f_bit      = ~i;   endfunction
   function int         f_int     ; input int      i;  f_int      = ~i;   endfunction
   function byte        f_byte    ; input byte     i;  f_byte     = ~i;   endfunction
   function shortint    f_shortint; input shortint i;  f_shortint = ~i;   endfunction
   function longint     f_longint ; input longint  i;  f_longint  = ~i;   endfunction
   function chandle     f_chandle ; input chandle  i;  f_chandle  = i;   endfunction

   // Note there's no "input" here  vvvv, it's the default
   function bit         g_bit     (bit      i);  g_bit      = ~i;   endfunction
   function int         g_int     (int      i);  g_int      = ~i;   endfunction
   function byte        g_byte    (byte     i);  g_byte     = ~i;   endfunction
   function shortint    g_shortint(shortint i);  g_shortint = ~i;   endfunction
   function longint     g_longint (longint  i);  g_longint  = ~i;   endfunction
   function chandle     g_chandle (chandle  i);  g_chandle  = i;   endfunction

   chandle c;

   initial begin

      if (int123() !== 32'h123) $stop;

      if (f_bit(1'h1) !== 1'h0) $stop;
      if (f_bit(1'h0) !== 1'h1) $stop;
      if (f_int(32'h1) !== 32'hfffffffe) $stop;
      if (f_byte(8'h1) !== 8'hfe) $stop;
      if (f_shortint(16'h1) !== 16'hfffe) $stop;
      if (f_longint(64'h1) !== 64'hfffffffffffffffe) $stop;
      if (f_chandle(c) !== c) $stop;

      if (g_bit(1'h1) !== 1'h0) $stop;
      if (g_bit(1'h0) !== 1'h1) $stop;
      if (g_int(32'h1) !== 32'hfffffffe) $stop;
      if (g_byte(8'h1) !== 8'hfe) $stop;
      if (g_shortint(16'h1) !== 16'hfffe) $stop;
      if (g_longint(64'h1) !== 64'hfffffffffffffffe) $stop;
      if (g_chandle(c) !== c) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
