// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2019 by Wilson Snyder.

module t (/*AUTOARG*/);

   // verilator lint_off UNBOUNDED
   int q[$ : 3];

   initial begin
      q.push_front(1);
      q.push_front(1);
      q.push_front(1);
      if (q.size() != 3) $stop;
      q.push_front(1);
      // TODO correct answer when supported:
      //if (q.size() != 3) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
