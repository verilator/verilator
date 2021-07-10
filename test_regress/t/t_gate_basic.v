// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2004 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   integer cyc; initial cyc=1;

   reg [31:0] a;
   reg [31:0] b;

   wire [2:0] bf;  buf   BF0 (bf[0], a[0]),
                         BF1 (bf[1], a[1]),
                         BF2 (bf[2], a[2]);

   // verilator lint_off IMPLICIT
   not   #(0.108) NT0 (nt0, a[0]);
   and   #1       AN0 (an0, a[0], b[0]);
   nand  #(2,3)   ND0 (nd0, a[0], b[0], b[1]);
   or    OR0 (or0, a[0], b[0]);
   nor   NR0 (nr0, a[0], b[0], b[2]);
   xor       (xo0, a[0], b[0]);
   xnor      (xn0, a[0], b[0], b[2]);
   // verilator lint_on IMPLICIT

   parameter BITS=32;
   wire [BITS-1:0] ba;
   buf BARRAY [BITS-1:0] (ba, a);

`ifdef verilator
   specify
      specparam CDS_LIBNAME  = "foobar";
      (nt0 *> nt0) = (0, 0);
   endspecify

  specify
    // delay parameters
    specparam
      a$A1$Y = 1.0,
      b$A0$Z = 1.0;

    // path delays
    (A1 *> Q) = (a$A1$Y, a$A1$Y);
    (A0 *> Q) = (b$A0$Y, a$A0$Z);

    if (C1) (IN => OUT) = (1,1);
    ifnone (IN => OUT) = (2,2);

    showcancelled Q;
    noshowcancelled Q;
    pulsestyle_ondetect Q;
    pulsestyle_onevent Q;

    // other unimplemented stuff
    $fullskew();
    $hold();
    $nochange();
    $period();
    $recovery();
    $recrem();
    $removal();
    $setup();
    $setuphold();
    $skew();
    $timeskew();
    $width();

  endspecify
`endif

   always @ (posedge clk) begin
      if (cyc!=0) begin
         cyc <= cyc + 1;
         if (cyc==1) begin
            a <= 32'h18f6b034;
            b <= 32'h834bf892;
         end
         if (cyc==2) begin
            a <= 32'h529ab56f;
            b <= 32'h7835a237;
            if (bf !== 3'b100) $stop;
            if (nt0 !== 1'b1) $stop;
            if (an0 !== 1'b0) $stop;
            if (nd0 !== 1'b1) $stop;
            if (or0 !== 1'b0) $stop;
            if (nr0 !== 1'b1) $stop;
            if (xo0 !== 1'b0) $stop;
            if (xn0 !== 1'b1) $stop;
            if (ba != 32'h18f6b034) $stop;
         end
         if (cyc==3) begin
            if (bf !== 3'b111) $stop;
            if (nt0 !== 1'b0) $stop;
            if (an0 !== 1'b1) $stop;
            if (nd0 !== 1'b0) $stop;
            if (or0 !== 1'b1) $stop;
            if (nr0 !== 1'b0) $stop;
            if (xo0 !== 1'b0) $stop;
            if (xn0 !== 1'b0) $stop;
         end
         if (cyc==4) begin
            $write("*-* All Finished *-*\n");
            $finish;
         end
      end
   end

endmodule
