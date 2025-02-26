// DESCRIPTION: Verilator: Test automatic function variables lifetime
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Augustin Fabre.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

// Bug5747: Make sure that a variable with automatic storage is freshly
// allocated when entering the function.

module t();
   function automatic int ts_queue();
      static int qs[$];
      qs.push_back(0);
      // $display("  qs: %p", qs);
      return qs.size();
   endfunction

   function automatic int t_queue();
      int q[$];
      q.push_back(0);
      // $display("  q: %p", q);
      return q.size();
   endfunction

   function automatic int t_scalar();
      int x;
      ++x;
      return x;
   endfunction

   typedef struct {
      int y;
   } y_t;

   function automatic int t_struct();
      y_t y;
      ++y.y;
      return y.y;
   endfunction

   function automatic string t_string();
      string x;
      x = {x, "s"};
      return x;
   endfunction

class ClsZ;
   int z;
endclass

   function automatic int t_class();
      ClsZ z = new();
      ++z.z;
      return z.z;
   endfunction

   typedef string dyn_t[];
   function automatic dyn_t t_dyn();
      dyn_t x;
      x = {x, "s"};
      return x;
   endfunction

   typedef string assoc_t[int];
   function automatic assoc_t t_assoc();
      static int ins = 0;
      assoc_t x;
      ins = ins + 1;
      x[ins] = "s";
      return x;
   endfunction

   typedef string wild_t[*];
   function automatic wild_t t_wild();
      static int ins = 0;
      wild_t x;
      ins = ins + 1;
      x[ins] = "s";
      return x;
   endfunction

   typedef int unpack_t[8];
   function automatic unpack_t t_unpack();
      static int ins = 0;
      unpack_t x;
      ins = ins + 1;
      x[ins] = ins;
      return x;
   endfunction

   // =======================

   function automatic void main();
      for (int i = 0; i < 3; ++i) begin
         int qn = ts_queue();
         int qo = ts_queue();
         `checkh(qn, i * 2 + 1);
         `checkh(qo, i * 2 + 2);
      end

      for (int i = 0; i < 3; ++i) begin
         int qn = t_queue();
         `checkh(qn, 1);
      end

      for (int i = 0; i < 3; ++i) begin
         int x = t_scalar();
         `checkh(x, 1);
      end

      for (int i = 0; i < 3; ++i) begin
         int y = t_struct();
         `checkh(y, 1);
      end

      for (int i = 0; i < 3; ++i) begin
         int z = t_class();
         `checkh(z, 1);
      end

      for (int i = 0; i < 3; ++i) begin
         string z = t_string();
         `checks(z, "s");
      end

      for (int i = 0; i < 3; ++i) begin
         dyn_t z = t_dyn();
         `checkh(z.size(), 1);
      end

      for (int i = 0; i < 3; ++i) begin
         assoc_t z = t_assoc();
         `checkh(z.size(), 1);
      end

      for (int i = 0; i < 3; ++i) begin
         wild_t z = t_wild();
         `checkh(z.size(), 1);
      end

      for (int i = 0; i < 3; ++i) begin
         int cnt;
         unpack_t z = t_unpack();
         cnt = 0;
         for (int j = 0; j < $high(z); ++j) begin
            if (z[j] != 0) cnt = cnt + 1;
         end
         `checkh(cnt, 1);
      end

   endfunction

   initial begin
      main();
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
