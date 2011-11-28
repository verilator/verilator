// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2009 by Wilson Snyder.

module t;

   // Arguable, but we won't throw a hidden warning on tcp_port
   parameter tcp_port  = 5678;
   import "DPI-C" function int dpii_func ( input integer  tcp_port,
                                           output longint obj );
   // 't' is hidden:
   integer t;

endmodule
