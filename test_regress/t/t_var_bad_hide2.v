// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2009 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

   // Arguable, but we won't throw a hidden warning on tcp_port
   parameter tcp_port  = 5678;
   import "DPI-C" function int dpii_func ( input integer  tcp_port,
                                           output longint obj );
   // 't' is hidden:
   integer t;

endmodule
