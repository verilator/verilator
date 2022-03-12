// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer cyc = 0;

   integer i;
   string  v;

   // verilator lint_off UNUSED
   integer unused[];
   // verilator lint_on UNUSED

   typedef bit [7:0] byte_t;
   byte_t a[];
   byte_t b[];

  // wide data array
   typedef struct packed {
     logic [15:0]  header;
     logic [223:0] payload;
     logic [15:0]  checksum;
   } pck256_t;

   pck256_t p256[];

   string          s[] = { "hello", "sad", "world" };

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      begin
         `checkh(a.size, 0);
         v = $sformatf("%p", a); `checks(v, "'{}");

         `checkh(s.size, 3);
         `checks(s[0], "hello");
         `checks(s[1], "sad");
         `checks(s[2], "world");

         a = new [3];
         `checkh(a.size, 3);
         a[0] = 10;
         a[1] = 11;
         a[2] = 12;
         `checkh(a[0], 10);
         `checkh(a[1], 11);
         `checkh(a[2], 12);
         v = $sformatf("%p", a); `checks(v, "'{'ha, 'hb, 'hc} ");
         a.delete;
         `checkh(a.size, 0);

         a = '{15, 16};
         `checkh(a.size, 2);
         `checkh(a[0], 15);
         `checkh(a[1], 16)

         a = {17, 18};
         `checkh(a.size, 2);
         `checkh(a[0], 17);
         `checkh(a[1], 18)

         a = '{17};
         `checkh(a.size, 1);  // IEEE says resizes to smallest that fits pattern
         `checkh(a[0], 17);

         a = new[2];
         a[0] = 5;
         a[1] = 6;
         `checkh(a[0], 5);
         `checkh(a[1], 6);
         a = new[2];
`ifdef verilator  // bug2618
         a[0] = 0;
         a[1] = 0;
`endif
         `checkh(a[0], 0);
         `checkh(a[1], 0);

         a[0] = 5;
         a[1] = 6;
         `checkh(a[0], 5);
         `checkh(a[1], 6);

         b = new [4](a);
         `checkh(b.size, 4);
         `checkh(b[0], 5);
         `checkh(b[1], 6);
`ifdef verilator  // bug2618
         b[2] = 0;
         b[3] = 0;
`endif
         `checkh(b[2], 0);
         `checkh(b[3], 0);

         a = b;
         `checkh(a.size, 4);
         `checkh(a[0], 5);
         `checkh(a[1], 6);
         `checkh(a[2], 0);
         `checkh(a[3], 0);

         a = new [0];
         `checkh(a.size, 0);
         b = new [4](a);
         `checkh(b.size, 4);
`ifdef verilator  // bug2618
         b[0] = 0;
         b[1] = 0;
         b[2] = 0;
         b[3] = 0;
`endif
         `checkh(b[0], 0);
         `checkh(b[1], 0);
         `checkh(b[2], 0);
         `checkh(b[3], 0);

         a = new[4] ('{8'd1,8'd2,8'd3,8'd4});
         `checkh(a.size, 4);
         `checkh(a[0], 1);
         `checkh(a[1], 2);
         `checkh(a[2], 3);
         `checkh(a[3], 4);

         i = 0;
         foreach (a[j]) i += int'(a[j]);
         `checkh(i, 1 + 2 + 3 + 4);

         // test wide dynamic array
         p256 = new [11];
         `checkh(p256.size, 11);
         `checkh(p256.size(), 11);

         p256[1].header   = 16'hcafe;
         p256[1].payload  = {14{16'hbabe}};
         p256[1].checksum = 16'hdead;
         `checkh(p256[1].header, 16'hcafe);
         `checkh(p256[1], {16'hcafe,{14{16'hbabe}},16'hdead});

         //X's: `checkh(p256[0], 'x);

         p256[5] = '1;
         `checkh(p256[5], {32{8'hff}});

         p256[5].header = 16'h2;
         `checkh(p256[5], {16'h2,{30{8'hff}}});

         p256[2] = ( p256[5].header == 2 ) ? p256[1] : p256[5];
         `checkh(p256[2], {16'hcafe,{14{16'hbabe}},16'hdead});


         p256.delete();
         `checkh(p256.size, 0);

      end

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
