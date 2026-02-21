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

module sub (intf single_intf_port);
  localparam byte  single_foo_bar_byte = single_intf_port.FOO.BAR_ARRAY[3];

  initial begin
    #1;
    `checkd(single_foo_bar_byte, 8'd8);
  end
endmodule

module t ();
  intf single_intf ();

  sub
  the_sub (
      .single_intf_port(single_intf)
  );

  initial begin
    #2;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
