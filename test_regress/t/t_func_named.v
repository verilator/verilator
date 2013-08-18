// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2013 by Wilson Snyder.

module t (/*AUTOARG*/);

   function int f( int j = 1, int s = 0 );
      return (j<<16) | s;
   endfunction

`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

   initial begin
      `checkh( f(.j(2), .s(1))	, 32'h2_0001 );
      `checkh( f(.s(1))		, 32'h1_0001 );
      `checkh( f(, 1)		, 32'h1_0001 );
      `checkh( f(.j(2))		, 32'h2_0000 );
      `checkh( f(.s(1), .j(2))	, 32'h2_0001 );
      `checkh( f(.s(), .j())	, 32'h1_0000 );
      `checkh( f(2)		, 32'h2_0000 );
      `checkh( f()		, 32'h1_0000 );

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
