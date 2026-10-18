// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

module t;

  // Issue #3198 reproducer, unsized packed dimension as the sole packed dimension
  import "DPI-C" function int dpii_failure();
  import "DPI-C" function void dpii_action(
    output bit [] res,
    input bit [] arg0,
    input int arg1
  );
  import "DPI-C" function int dpii_width(
    input logic [] arg0,
    input int dim
  );
  import "DPI-C" function int dpii_size(
    input bit signed [] arg0[],
    input int dim
  );

  initial begin
    bit [6:0] res7;
    bit [6:0] arg7;
    bit [32:1] res32;
    bit [32:1] arg32;
    logic [64:0] arg65;
    bit [2:0][4:0] pack2d;
    bit [14:0] unp[3];

    arg7 = 7'h2d;
    arg32 = 32'h12345678;
    arg65 = 65'h1_0000_0000_0000_0001;
    pack2d = 15'h5a5a;
    unp[0] = 15'h1;
    unp[1] = 15'h2;
    unp[2] = 15'h3;
    dpii_action(res7, arg7, 7);
    `checkh(res7, ~arg7);
    dpii_action(res32, arg32, 32);
    `checkh(res32, ~arg32);

    `checkd(dpii_width(arg65, 0), 65);
    `checkd(dpii_width(arg7, 0), 7);
    `checkd(dpii_width(pack2d, 0), 15);
    `checkd(dpii_size(unp, 1), 3);

    `checkd(dpii_failure(), 0);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
