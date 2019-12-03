// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2019 by Wilson Snyder.

module t (/*AUTOARG*/);

   initial begin
      string a [string];
      string k;
      string v;

      v = a.num("badarg");
      v = a.size("badarg");
      v = a.exists();  // Bad
      v = a.exists(k, "bad2");
      v = a.first();  // Bad
      v = a.next(k, "bad2");  // Bad
      v = a.last();  // Bad
      v = a.prev(k, "bad2");  // Bad
      a.delete(k, "bad2");
   end
endmodule
