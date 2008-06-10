// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003 by Wilson Snyder.

module t;
   function recurse;
      input i;
      recurse = recurse2(i);
   endfunction

   function recurse2;
      input i;
      recurse2 = recurse(i);
   endfunction

endmodule
