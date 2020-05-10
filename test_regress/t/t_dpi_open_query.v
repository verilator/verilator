// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2020 by Geza Lore. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

`define check(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0)
`define unless(cond,gotv,expv) do if (!(cond)) `check(gotv, expv); while(0)

`ifdef VERILATOR
 `define NO_DYNAMIC
 `define NO_QUEUE
`endif

`ifdef VCS
 `define NO_QUEUE
`endif

`ifdef NC
 `define NO_DYNAMIC
 `define NO_QUEUE
`endif

`ifdef NC
 `define ONNC 1
`else
 `define ONNC 0
`endif

`ifdef MS
 `define ONMS 1
`else
 `define ONMS 0
`endif

module t;

   // 1 open dimension
   import "DPI-C" function int cSvLeft1(       input bit h [], int d);
   import "DPI-C" function int cSvRight1(      input bit h [], int d);
   import "DPI-C" function int cSvLow1(        input bit h [], int d);
   import "DPI-C" function int cSvHigh1(       input bit h [], int d);
   import "DPI-C" function int cSvIncrement1(  input bit h [], int d);
   import "DPI-C" function int cSvSize1(       input bit h [], int d);
   import "DPI-C" function int cSvDimensions1( input bit h []);

   // 2 open dimensions
   import "DPI-C" function int cSvLeft2(       input bit h [][], int d);
   import "DPI-C" function int cSvRight2(      input bit h [][], int d);
   import "DPI-C" function int cSvLow2(        input bit h [][], int d);
   import "DPI-C" function int cSvHigh2(       input bit h [][], int d);
   import "DPI-C" function int cSvIncrement2(  input bit h [][], int d);
   import "DPI-C" function int cSvSize2(       input bit h [][], int d);
   import "DPI-C" function int cSvDimensions2( input bit h [][]);

   // 3 open dimensions
   import "DPI-C" function int cSvLeft3(       input bit h [][][], int d);
   import "DPI-C" function int cSvRight3(      input bit h [][][], int d);
   import "DPI-C" function int cSvLow3(        input bit h [][][], int d);
   import "DPI-C" function int cSvHigh3(       input bit h [][][], int d);
   import "DPI-C" function int cSvIncrement3(  input bit h [][][], int d);
   import "DPI-C" function int cSvSize3(       input bit h [][][], int d);
   import "DPI-C" function int cSvDimensions3( input bit h [][][]);

   // 4 open dimensions
   import "DPI-C" function int cSvLeft4(       input bit h [][][][], int d);
   import "DPI-C" function int cSvRight4(      input bit h [][][][], int d);
   import "DPI-C" function int cSvLow4(        input bit h [][][][], int d);
   import "DPI-C" function int cSvHigh4(       input bit h [][][][], int d);
   import "DPI-C" function int cSvIncrement4(  input bit h [][][][], int d);
   import "DPI-C" function int cSvSize4(       input bit h [][][][], int d);
   import "DPI-C" function int cSvDimensions4( input bit h [][][][]);

   // verilator lint_off UNDRIVEN
   bit  a1 [1:0];
   bit  a2 [1:0][2:0];
   bit  a3 [1:0][2:0][3:0];
   bit  a4 [1:0][2:0][3:0][4:0];

   bit  b1 [0:1];
   bit  b2 [0:1][0:2];
   bit  b3 [0:1][0:2][0:3];
   bit  b4 [0:1][0:2][0:3][0:4];

   bit  c1 [-1:1];
   bit  c2 [-1:1][-2:2];
   bit  c3 [-1:1][-2:2][-3:3];
   bit  c4 [-1:1][-2:2][-3:3][-4:4];

`ifndef NO_DYNAMIC
   bit  d1 [];
   bit  d2 [][-2:2];
   bit  d3 [][-2:2][-3:3];
   bit  d4 [][-2:2][-3:3][-4:4];
`endif

`ifndef NO_QUEUE
   bit  e1 [$];
`endif
   // verilator lint_on UNDRIVEN

   initial begin
`ifndef NO_DYNAMIC
      d1 = new[3];
      d2 = new[3];
      d3 = new[3];
      d4 = new[3];
`endif

`ifndef NO_QUEUE
      e1.push_back(0);
      e1.push_back(0);
      e1.push_back(0);
`endif

      // 1 open dimension
      `check(cSvDimensions1(a1), 1);
      `check(cSvDimensions1(b1), 1);
      `check(cSvDimensions1(c1), 1);
`ifndef NO_DYNAMIC
      `check(cSvDimensions1(d1), 1);
`endif
`ifndef NO_QUEUE
      `check(cSvDimensions1(e1), 1);
`endif
      for (int d = 0 ; d < 2 ; d++) begin
         if (`ONNC && d == 0) continue;

         `check(cSvLeft1(a1, d), d);
         `check(cSvRight1(a1, d), 0);
         `check(cSvLow1(a1, d), 0);
         `check(cSvHigh1(a1, d), d);
         `unless(`ONMS && d == 0, cSvIncrement1(a1, d), 1);
         `check(cSvSize1(a1, d), d+1);

         `check(cSvLeft1(b1, d), 0);
         `check(cSvRight1(b1, d), d);
         `check(cSvLow1(b1, d), 0);
         `check(cSvHigh1(b1, d), d);
`ifndef NC
         `unless(`ONMS && d == 0, cSvIncrement1(b1, d), d == 0 ? 1 : -1);
`endif
         `check(cSvSize1(b1, d), d+1);

         `check(cSvLeft1(c1, d), -d);
         `check(cSvRight1(c1, d), d);
         `check(cSvLow1(c1, d), -d);
         `check(cSvHigh1(c1, d), d);
`ifndef NC
         `unless(`ONMS && d == 0, cSvIncrement1(c1, d), d == 0 ? 1 : -1);
`endif
         `check(cSvSize1(c1, d), 2*d+1);

`ifndef NO_DYNAMIC
         `check(cSvLeft1(d1, d), d == 1 ? 0 : -d);
         `check(cSvRight1(d1, d), d == 1 ? 2 : d);
         `check(cSvLow1(d1, d), d == 1 ? 0 : -d);
         `check(cSvHigh1(d1, d), d == 1 ? 2 : d);
         `unless(`ONMS && d == 0, cSvIncrement1(d1, d), d == 0 ? 1 : -1);
         `check(cSvSize1(d1, d), 2*d+1);
`endif

`ifndef NO_QUEUE
         `check(cSvLeft1(e1, d), d == 1 ? 0 : -d);
         `check(cSvRight1(e1, d), d == 1 ? 2 : d);
         `check(cSvLow1(e1, d), d == 1 ? 0 : -d);
         `check(cSvHigh1(e1, d), d == 1 ? 2 : d);
         `unless(`ONMS && d == 0, cSvIncrement1(e1, d), d == 0 ? 1 : -1);
         `check(cSvSize1(e1, d), 2*d+1);
`endif
      end

      // 2 open dimensions
      `check(cSvDimensions2(a2), 2);
      `check(cSvDimensions2(b2), 2);
      `check(cSvDimensions2(c2), 2);
`ifndef NO_DYNAMIC
      `check(cSvDimensions2(d2), 2);
`endif
      for (int d = 0 ; d < 3 ; d++) begin
         if (`ONNC && d == 0) continue;

         `check(cSvLeft2(a2, d), d);
         `check(cSvRight2(a2, d), 0);
         `check(cSvLow2(a2, d), 0);
         `check(cSvHigh2(a2, d), d);
         `unless(`ONMS && d == 0, cSvIncrement2(a2, d), 1);
         `check(cSvSize2(a2, d), d+1);

         `check(cSvLeft2(b2, d), 0);
         `check(cSvRight2(b2, d), d);
         `check(cSvLow2(b2, d), 0);
         `check(cSvHigh2(b2, d), d);
`ifndef NC
         `unless(`ONMS && d == 0, cSvIncrement2(b2, d), d == 0 ? 1 : -1);
`endif
         `check(cSvSize2(b2, d), d+1);

         `check(cSvLeft2(c2, d), -d);
         `check(cSvRight2(c2, d), d);
         `check(cSvLow2(c2, d), -d);
         `check(cSvHigh2(c2, d), d);
`ifndef NC
         `unless(`ONMS && d == 0, cSvIncrement2(c2, d), d == 0 ? 1 : -1);
`endif
         `check(cSvSize2(c2, d), 2*d+1);

`ifndef NO_DYNAMIC
         `check(cSvLeft2(d2, d), d == 1 ? 0 : -d);
         `check(cSvRight2(d2, d), d == 1 ? 2 : d);
         `check(cSvLow2(d2, d), d == 1 ? 0 : -d);
         `check(cSvHigh2(d2, d), d == 1 ? 2 : d);
         `unless(`ONMS && d == 0, cSvIncrement2(d2, d), d == 0 ? 1 : -1);
         `check(cSvSize2(d2, d), 2*d+1);
`endif
      end

      // 3 open dimensions
      `check(cSvDimensions3(a3), 3);
      `check(cSvDimensions3(b3), 3);
      `check(cSvDimensions3(c3), 3);
`ifndef NO_DYNAMIC
      `check(cSvDimensions3(d3), 3);
`endif
      for (int d = 0 ; d < 4 ; d++) begin
         if (`ONNC && d == 0) continue;

         `check(cSvLeft3(a3, d), d);
         `check(cSvRight3(a3, d), 0);
         `check(cSvLow3(a3, d), 0);
         `check(cSvHigh3(a3, d), d);
         `unless(`ONMS && d == 0, cSvIncrement3(a3, d), 1);
         `check(cSvSize3(a3, d), d+1);

         `check(cSvLeft3(b3, d), 0);
         `check(cSvRight3(b3, d), d);
         `check(cSvLow3(b3, d), 0);
         `check(cSvHigh3(b3, d), d);
`ifndef NC
         `unless(`ONMS && d == 0, cSvIncrement3(b3, d), d == 0 ? 1 : -1);
`endif
         `check(cSvSize3(b3, d), d+1);

         `check(cSvLeft3(c3, d), -d);
         `check(cSvRight3(c3, d), d);
         `check(cSvLow3(c3, d), -d);
         `check(cSvHigh3(c3, d), d);
`ifndef NC
         `unless(`ONMS && d == 0, cSvIncrement3(c3, d), d == 0 ? 1 : -1);
`endif
         `check(cSvSize3(c3, d), 2*d+1);

`ifndef NO_DYNAMIC
         `check(cSvLeft3(d3, d), d == 1 ? 0 : -d);
         `check(cSvRight3(d3, d), d == 1 ? 2 : d);
         `check(cSvLow3(d3, d), d == 1 ? 0 : -d);
         `check(cSvHigh3(d3, d), d == 1 ? 2 : d);
         `unless(`ONMS && d == 0, cSvIncrement3(d3, d), d == 0 ? 1 : -1);
         `check(cSvSize3(d3, d), 2*d+1);
`endif
      end

      // 4 open dimension
      `check(cSvDimensions4(a4), 4);
      `check(cSvDimensions4(b4), 4);
      `check(cSvDimensions4(c4), 4);
`ifndef NO_DYNAMIC
      `check(cSvDimensions4(d4), 4);
`endif
      for (int d = 0 ; d < 5 ; d++) begin
         if (`ONNC && d == 0) continue;

         `check(cSvLeft4(a4, d), d);
         `check(cSvRight4(a4, d), 0);
         `check(cSvLow4(a4, d), 0);
         `check(cSvHigh4(a4, d), d);
         `unless(`ONMS && d == 0, cSvIncrement4(a4, d), 1);
         `check(cSvSize4(a4, d), d+1);

         `check(cSvLeft4(b4, d), 0);
         `check(cSvRight4(b4, d), d);
         `check(cSvLow4(b4, d), 0);
         `check(cSvHigh4(b4, d), d);
`ifndef NC
         `unless(`ONMS && d == 0, cSvIncrement4(b4, d), d == 0 ? 1 : -1);
`endif
         `check(cSvSize4(b4, d), d+1);

         `check(cSvLeft4(c4, d), -d);
         `check(cSvRight4(c4, d), d);
         `check(cSvLow4(c4, d), -d);
         `check(cSvHigh4(c4, d), d);
`ifndef NC
         `unless(`ONMS && d == 0, cSvIncrement4(c4, d), d == 0 ? 1 : -1);
`endif
         `check(cSvSize4(c4, d), 2*d+1);

`ifndef NO_DYNAMIC
         `check(cSvLeft4(d4, d), d == 1 ? 0 : -d);
         `check(cSvRight4(d4, d), d == 1 ? 2 : d);
         `check(cSvLow4(d4, d), d == 1 ? 0 : -d);
         `check(cSvHigh4(d4, d), d == 1 ? 2 : d);
         `unless(`ONMS && d == 0, cSvIncrement4(d4, d), d == 0 ? 1 : -1);
         `check(cSvSize4(d4, d), 2*d+1);
`endif
      end

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
