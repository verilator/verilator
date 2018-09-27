// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2016 by Wilson Snyder.

module t;
   sub sub ();
endmodule

module sub;
   //verilator no_inline_module
   string scope;
   initial begin
      scope = $sformatf("%m");
      $write("[%0t] In %s\n", $time, scope);
`ifdef VERILATOR
      if (scope != "top.l2Name.sub") $stop;
`else
      if (scope != "top.t.sub") $stop;
`endif
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
