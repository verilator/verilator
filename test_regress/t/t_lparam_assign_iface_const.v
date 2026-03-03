// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

typedef struct {
    int BAR_INT;
    bit BAR_BIT;
    byte BAR_ARRAY [0:3];
} foo_t;

interface intf
  #(parameter foo_t FOO = '{4, 1'b1, '{8'd1, 8'd2, 8'd4, 8'd8}})
    ();
endinterface

module sub (intf the_intf_port [4]);
  localparam int   intf_foo_bar_int  = the_intf_port[0].FOO.BAR_INT;

  initial begin
    #1;
    if (intf_foo_bar_int  != 4) $stop;
  end
endmodule

module t ();
  intf the_intf [4] ();

  sub
  the_sub (
      .the_intf_port   (the_intf)
  );

  initial begin
    #2;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
