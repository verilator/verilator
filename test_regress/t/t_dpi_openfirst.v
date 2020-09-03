// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2017 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

`ifdef VERILATOR
 `define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0)
`else
 `define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); end while(0)
`endif

module t (/*AUTOARG*/);

   int i_i [2:0];
   int o_i [2:0];

   import "DPI-C" function int dpii_failure();
   import "DPI-C" function void dpii_open_i(input int i [], output int o []);

   reg [95:0] crc;

   initial begin
      crc = 96'h8a10a572_5aef0c8d_d70a4497;

      i_i[0] = crc[31:0];
      i_i[1] = crc[63:32];
      i_i[2] = crc[95:64];
      dpii_open_i(i_i, o_i);
      `checkh(o_i[0], ~i_i[0]);
      `checkh(o_i[1], ~i_i[1]);
      `checkh(o_i[2], ~i_i[2]);

      if (dpii_failure()!=0) begin
         $write("%%Error: Failure in DPI tests\n");
         $stop;
      end
      else begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
