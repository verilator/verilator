// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Methods defined by IEEE:
//  class mailbox #(type T = dynamic_singular_type) ;
//     function new(int bound = 0);
//     function int num();
//     task put( T message);
//     function int try_put( T message);
//     task get( ref T message );
//     function int try_get( ref T message );
//     task peek( ref T message );
//     function int try_peek( ref T message );
//  endclass

`ifndef MAILBOX_T
 `define MAILBOX_T mailbox
`endif

// verilator lint_off DECLFILENAME
module t(/*AUTOARG*/);
   `MAILBOX_T #(int) m;

   initial begin
      m = new(4);
      if (m.num() != 0) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
