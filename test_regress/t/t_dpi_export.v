// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2009 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

`ifdef VCS
 `define NO_TIME
`endif
`ifdef NC
 `define NO_TIME
`endif

module t;

   sub a (.inst(1));
   sub b (.inst(2));

   // Returns integer line number, or -1 for all ok
   import "DPI-C" context function int dpix_run_tests();

   export "DPI-C" task dpix_t_int;
   task dpix_t_int(input int i, output int o);  o = ~i; endtask

   export "DPI-C" dpix_t_renamed = task dpix_t_ren;
   task dpix_t_ren(input int i, output int o);  o = i+2; endtask

   export "DPI-C" function dpix_int123;
   function int dpix_int123();  dpix_int123 = 32'h123;   endfunction

   export "DPI-C" function dpix_f_bit;
   export "DPI-C" function dpix_f_bit15;
   export "DPI-C" function dpix_f_int;
   export "DPI-C" function dpix_f_byte;
   export "DPI-C" function dpix_f_shortint;
   export "DPI-C" function dpix_f_longint;
   export "DPI-C" function dpix_f_chandle;

   function bit         dpix_f_bit     (bit      i);   dpix_f_bit = ~i; endfunction
   function bit [14:0]  dpix_f_bit15   (bit [14:0] i); dpix_f_bit15 = ~i; endfunction
   function int         dpix_f_int     (int      i);   dpix_f_int = ~i; endfunction
   function byte        dpix_f_byte    (byte     i);   dpix_f_byte = ~i; endfunction
   function shortint    dpix_f_shortint(shortint i);   dpix_f_shortint = ~i; endfunction
   function longint     dpix_f_longint (longint  i);   dpix_f_longint = ~i; endfunction
   function chandle     dpix_f_chandle (chandle  i);   dpix_f_chandle = i; endfunction

   export "DPI-C" task dpix_t_bit48;
   task dpix_t_bit48(input bit [47:0] i, output bit [47:0] o);  o = ~i; endtask
   export "DPI-C" task dpix_t_bit95;
   task dpix_t_bit95(input bit [94:0] i, output bit [94:0] o);  o = ~i; endtask
   export "DPI-C" task dpix_t_bit96;
   task dpix_t_bit96(input bit [95:0] i, output bit [95:0] o);  o = ~i; endtask

   export "DPI-C" task dpix_t_reg;
   task dpix_t_reg(input reg i, output reg o);  o = ~i; endtask
   export "DPI-C" task dpix_t_reg15;
   task dpix_t_reg15(input reg [14:0] i, output reg [14:0] o);  o = ~i; endtask
   export "DPI-C" task dpix_t_reg95;
   task dpix_t_reg95(input reg [94:0] i, output reg [94:0] o);  o = ~i; endtask
   export "DPI-C" task dpix_t_integer;
   task dpix_t_integer(input integer i, output integer o);  o = ~i; endtask
`ifndef NO_TIME
   export "DPI-C" task dpix_t_time;
`endif
   task dpix_t_time(input time i, output time o);  o = ~i; endtask

   int lineno;

   initial begin
      lineno = dpix_run_tests();
      if (lineno != -1) begin
         $display("[%0t] %%Error: t_dpix_ort_c.c:%0d: dpix_run_tests returned an error", $time, lineno);
         $stop;
      end

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule

module sub (input int inst);

   export "DPI-C" function dpix_sub_inst;

   function int dpix_sub_inst (int i);  dpix_sub_inst  = inst + i;   endfunction

endmodule
