// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2011 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

`define is_near_real(a,b)  (( ((a)<(b)) ? (b)-(a) : (a)-(b)) < (((a)/(b))*0.0001))
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer cyc = 0;

   real    r;
   reg [31:0] v32;
   reg [63:0] v64;
   reg [95:0] v96;

   initial begin
      // verilator lint_off REALCVT
      v32 = -1.5;
      v64 = -1.5;
      v96 = -1.5;
      // verilator lint_on REALCVT
      `checkh(v32, 32'hfffffffe);
      `checkh(v64, 64'hfffffffffffffffe);
      `checkh(v96, 96'hfffffffffffffffffffffffe);

      // verilator lint_off REALCVT
      v32 = 12456789012345678912345.5;
      v64 = 12456789012345678912345.5;
      v96 = 12456789012345678912345.5;
      // verilator lint_on REALCVT
      `checkh(v32, 32'he5400000);
      `checkh(v64, 64'h48acb7d4e5400000);
      `checkh(v96, 96'h000002a348acb7d4e5400000);

      // verilator lint_off REALCVT
      v32 = -12456789012345678912345.5;
      v64 = -12456789012345678912345.5;
      v96 = -12456789012345678912345.5;
      // verilator lint_on REALCVT
      `checkh(v32, 32'h1ac00000);
      `checkh(v64, 64'hb753482b1ac00000);
      `checkh(v96, 96'hfffffd5cb753482b1ac00000);
   end

   // Test loop
   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 10) begin
         r <= 0;
      end
      else if (cyc == 11) begin
         // verilator lint_off REALCVT
         v32 = r;
         v64 = r;
         v96 = r;
         // verilator lint_on REALCVT
         `checkh(v32, '0);
         `checkh(v64, '0);
         `checkh(v96, '0);
      end
      else if (cyc == 20) begin
         r <= -5.24567;
      end
      else if (cyc == 21) begin
         // verilator lint_off REALCVT
         v32 = r;
         v64 = r;
         v96 = r;
         // verilator lint_on REALCVT
         `checkh(v32, 32'hfffffffb);
         `checkh(v64, 64'hfffffffffffffffb);
         `checkh(v96, 96'hfffffffffffffffffffffffb);
      end
      else if (cyc == 30) begin
         r <= 12456789012345678912345.5;
      end
      else if (cyc == 31) begin
         // verilator lint_off REALCVT
         v32 = r;
         v64 = r;
         v96 = r;
         // verilator lint_on REALCVT
         `checkh(v32, 32'he5400000);
         `checkh(v64, 64'h48acb7d4e5400000);
         `checkh(v96, 96'h000002a348acb7d4e5400000);
      end
      else if (cyc == 99) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
