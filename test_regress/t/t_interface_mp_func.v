// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2014 by Wilson Snyder.

interface pads_if();
   modport mp_dig(
		  import        fIn,
		  import        fOut );

   integer exists[8];
   function automatic integer fIn (integer i);
      fIn = exists[i];
   endfunction
   task automatic fOut (integer i);
      exists[i] = 33;
   endtask
endinterface

module t();
   pads_if padsif();
   initial begin
      padsif.fOut(3);
      if (padsif.fIn(3) != 33) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
