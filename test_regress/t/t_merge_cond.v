// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Geza Lore.
// SPDX-License-Identifier: CC0-1.0

`define check(got ,exp) do if ((got) !== (exp)) begin $write("%%Error: %s:%0d: cyc=%0d got='h%x exp='h%x\n", `__FILE__,`__LINE__, cyc, (got), (exp)); $stop; end while(0)

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer cyc=0;
   reg [63:0] crc= 64'h5aef0c8d_d70a4497;
   reg [63:0] prev_crc;

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63]^crc[2]^crc[0]};

      prev_crc <= crc;
      if (cyc==99) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

   wire cond2 = &crc[1:0];
   wire cond3 = &crc[2:0];

   reg  shuf_q [63:0];

   always @(posedge clk) begin
      reg bits [63:0];
      reg shuf_a [63:0];
      reg shuf_b [63:0];
      reg shuf_c [63:0];
      reg shuf_d [63:0];
      reg shuf_e [63:0];

      // Unpack these to test core algorithm
      for (int i = 0; i < 64; i = i + 1) begin
         bits[i] = crc[i];
      end

      for (int i = 0; i < 64; i = i + 1) begin
         shuf_a[i] = cyc[0] ? bits[i] : bits[63-i];
      end

      if (cyc[1]) begin
         for (int i = 0; i < 64; i = i + 1) begin
            shuf_b[i] = cyc[0] ? bits[i] : bits[63-i];
         end
      end else begin
         for (int i = 0; i < 64; i = i + 1) begin
            shuf_b[i] = cyc[0] ? bits[63-i] : bits[i];
         end
      end

      // Also test merge under clean/bit extract
      for (int i = 0; i < 64; i = i + 1) begin
         shuf_c[i] = cyc[0] ? crc[i] : crc[63-i];
      end

      // Merge with 'cond & value', 'value & cond', or 'cond'
      shuf_d[0] = cond2 ? bits[0] : bits[63];
      for (int i = 1; i < 32; i = i + 2) begin
         shuf_d[i] = cond2 & bits[i];
      end
      for (int i = 2; i < 32; i = i + 2) begin
         shuf_d[i] = bits[i] & cond2;
      end
      for (int i = 32; i < 64; i = i + 1) begin
         shuf_d[i] = cond2;
      end

      // Merge with an '&' also used for masking of LSB.
      shuf_e[0] = cond3 ? bits[0] : bits[63];
      for (int i = 1; i < 64; i = i + 1) begin
         shuf_e[i] = cond3 & crc[0];
      end

      // Also delayed..
      for (int i = 0; i < 64; i = i + 1) begin
         shuf_q[i] <= cyc[0] ? crc[i] : crc[63-i];
      end

      // Check results

      if (cyc[0]) begin
         for (int i = 0; i < 64; i = i + 1) `check(shuf_a[i], crc[i]);
      end else begin
         for (int i = 0; i < 64; i = i + 1) `check(shuf_a[i], crc[63-i]);
      end

      if (cyc[0] ~^ cyc[1]) begin
         for (int i = 0; i < 64; i = i + 1) `check(shuf_b[i], crc[i]);
      end else begin
         for (int i = 0; i < 64; i = i + 1) `check(shuf_b[i], crc[63-i]);
      end

      if (cyc[0]) begin
         for (int i = 0; i < 64; i = i + 1) `check(shuf_c[i], crc[i]);
      end else begin
         for (int i = 0; i < 64; i = i + 1) `check(shuf_c[i], crc[63-i]);
      end

      if (cond2) begin
         `check(shuf_d[0], crc[0]);
         for (int i = 1; i < 32; i = i + 1) `check(shuf_d[i], crc[i]);
         for (int i = 32; i < 63; i = i + 1) `check(shuf_d[i], 1'd1);
      end else begin
         `check(shuf_d[0], crc[63]);
         for (int i = 1; i < 32; i = i + 1) `check(shuf_d[i], 1'b0);
         for (int i = 32; i < 63; i = i + 1) `check(shuf_d[i], 1'd0);
      end

      if (cond3) begin
         `check(shuf_e[0], crc[0]);
         for (int i = 1; i < 63; i = i + 1) `check(shuf_e[i], crc[0]);
      end else begin
         `check(shuf_e[0], crc[63]);
         for (int i = 1; i < 63; i = i + 1) `check(shuf_e[i], 1'b0);
      end

      if (cyc > 0) begin
         if (~cyc[0]) begin
            for (int i = 0; i < 64; i = i + 1) `check(shuf_q[i], prev_crc[i]);
         end else begin
            for (int i = 0; i < 64; i = i + 1) `check(shuf_q[i], prev_crc[63-i]);
         end

         if (((cyc - 1) >> 1) % 2 == 1) begin
            for (int i = 0; i < 64; i = i + 1) `check(shuf_g[i], prev_crc[i]);
         end else begin
            for (int i = 0; i < 64; i = i + 1) `check(shuf_g[i], prev_crc[63-i]);
         end
      end

      if (cyc[2]) begin
         for (int i = 0; i < 64; i = i + 1) `check(shuf_w[i], crc[i]);
      end else begin
         for (int i = 0; i < 64; i = i + 1) `check(shuf_w[i], crc[63-i]);
      end
   end

   // Generated always
   reg shuf_g [63:0];
   generate for (genvar i = 0 ; i < 64; i = i + 1)
     always @(posedge clk) begin
        shuf_g[i] <= cyc[1] ? crc[i] : crc[63-i];
     end
   endgenerate

   // Generated assign
   wire shuf_w [63:0];
   generate for (genvar i = 0 ; i < 64; i = i + 1)
     assign shuf_w[i] = cyc[2] ? crc[i] : crc[63-i];
   endgenerate

   // Things not to merge
   always @(posedge clk) begin
      reg  x;
      reg  y;
      reg  z;
      reg  w;

      // Do not merge if condition appears in an LVALUE
      x = crc[0];
      y = x ? crc[2] : crc[1];
      x = x ? crc[3] : crc[4];
      x = x ? crc[5] : crc[6];

      `check(x, (crc[0] ? crc[3] : crc[4]) ? crc[5] : crc[6]);
      `check(y, crc[0] ? crc[2] : crc[1]);

      // Do not merge if condition is not a pure expression
      $c("int _cnt = 0;");
      x = $c("_cnt++") ? crc[0] : crc[1];
      y = $c("_cnt++") ? crc[2] : crc[3];
      z = $c("_cnt++") ? crc[4] : crc[5];
      w = $c("_cnt++") ? crc[6] : crc[7];
      $c("if (_cnt != 4) abort();");

      `check(x, crc[1]);
      `check(y, crc[2]);
      `check(z, crc[4]);
      `check(w, crc[6]);
   end

endmodule
