// DESCRIPTION: Verilator: Using the wrong kind of interface in a portmap
// should cause an error
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2018 by Todd Strader.
// SPDX-License-Identifier: CC0-1.0

interface foo_intf;
   logic [7:0] a;
endinterface

interface bar_intf;
   logic [7:0] a;
endinterface

module foo_mod (foo_intf foo_port);
//  initial begin
//      $display("a = %0d", foo_port.a);
//  end
endmodule

module t (/*AUTOARG*/);

   foo_intf foo ();
   bar_intf bar ();

//   assign foo.a = 8'd1;
//   assign bar.a = 8'd2;

   foo_mod
   foo_mod (
      .foo_port (bar)
   );

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
