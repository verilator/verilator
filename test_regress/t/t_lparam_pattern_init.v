// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2010 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t (/*AUTOARG*/);

   localparam int unsigned SPI_INDEX = 0;
   localparam int unsigned I2C_INDEX = 1;
   localparam int unsigned TMR_INDEX = 4;

   localparam logic [31:0] AHB_ADDR[6] = '{
      SPI_INDEX: 32'h80001000,
      I2C_INDEX: 32'h80002000,
      TMR_INDEX: 32'h80003000,
      default: '0};

   initial begin
      `checkh(AHB_ADDR[0], 32'h80001000);
      `checkh(AHB_ADDR[1], 32'h80002000);
      `checkh(AHB_ADDR[2], 32'h0);
      `checkh(AHB_ADDR[3], 32'h0);
      `checkh(AHB_ADDR[4], 32'h80003000);
      `checkh(AHB_ADDR[5], 32'h0);
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
