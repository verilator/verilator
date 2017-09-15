// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003 by Wilson Snyder.

module m #(parameter int Foo);
endmodule

module t (/*AUTOARG*/);

   m #(10) foo();

   initial begin
    if (foo.Foo != 10) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
   end

endmodule
