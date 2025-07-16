// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2009 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

localparam UADDR_WIDTH = 4'd10;
localparam UROM_WIDTH = 5'd17;
localparam UROM_DEPTH = 11'd1024;


module t(
         input clk,
         input [UADDR_WIDTH-1:0] mAddr,
         output logic [UROM_WIDTH-1:0] mOutput);

   // Issue #3959
   reg [UROM_WIDTH-1:0] uRam[UROM_DEPTH];

   always @(posedge clk) mOutput <= uRam[mAddr];

   // Issue #6045
   typedef enum logic [1:0] { e_0, e_1, e_2, e_3 } enum_e;

   typedef struct packed {
      integer unsigned x;
      integer unsigned y;
   } foo_s;

   typedef struct packed {
      integer unsigned y;
   } bar_s;

   // Warning due to concatenation, but this is actually a member assignment
   localparam foo_s foo = '{
      y: (1 << e_0) | (1 << e_3)
      , default: '0
   };

   // No warning
   localparam bar_s bar = '{
      y: (1 << e_0) | (1 << e_3)
   };

endmodule
