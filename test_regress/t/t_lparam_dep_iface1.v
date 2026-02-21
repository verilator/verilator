// DESCRIPTION: Verilator: Get agregate type parameter from array of interfaces
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2026
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

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
    `checkd(intf_foo_bar_int, 4);
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
