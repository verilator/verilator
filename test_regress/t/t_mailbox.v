// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Methods defined by IEEE:
//  class mailbox #(type T = dynamic_singular_type) ;
//     function new(int bound = 0);
//     function int num();
//     task put( T message);
//     function int try_put( T message);
//     task get( ref T message );
//     function int try_get( ref T message );
//     task peek( ref T message );
//     function int try_peek( ref T message );
//  endclass

module t(/*AUTOARG*/);
   mailbox #(int) m;
   int     msg;
   int     out;

   initial begin
      m = new(4);
      if (m.num() != 0) $stop;
      if (m.try_get(msg) > 0) $stop;

      msg = 123;
      m.put(msg);
      msg = 0;
      if (m.num() != 1) $stop;
      if (m.try_peek(out) <= 0) $stop;
      if (out != 123) $stop;
      if (m.num() != 0) $stop;
      out = 0;
      if (m.try_peek(out) <= 0) $stop;
      if (out != 123) $stop;
      out = 0;
      if (m.try_get(out) <= 0) $stop;
      if (out != 123) $stop;
      if (m.num() != 0) $stop;

      msg = 124;
      m.put(msg);
      out = 0;
      m.get(out);
      if (out != 124) $stop;

      msg = 125;
      m.put(msg);
      m.put(msg);
      m.try_put(msg);
      m.try_put(msg);
      if (m.num() != 4) $stop;
      if (m.try_put(msg) != 0) $stop;
      if (m.num() != 4) $stop;
      m.get(out);
      m.get(out);
      m.get(out);
      m.get(out);
      if (m.num() != 0) $stop;

      fork
         begin
            #10;  // So later then get() starts below
            msg = 130;
            m.put(msg);
            msg = 131;
            m.put(msg);
         end
         begin
            if (m.try_get(msg) != 0) $stop;
            out = 0;
            m.get(out);  // Blocks until put
            if (out != 130) $stop;
            out = 0;
            m.get(out);
            if (out != 131) $stop;
         end
      join

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
