// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2024 by Antmicro. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module t(
   input [255:0] in,
   output [255:0] out
   );

   // do not optimize assignment
   logic tmp = $c(0);
   typedef logic[255:0] biguint;
   assign out = in + biguint'(tmp);

   always @(out) begin
      if (in !== 1) begin
         $write("'in' mismatch: (1 !== %d)\n", logic'(in));
         $stop;
      end
      else if (out !== 1) begin
         $write("'out' mismatch: (1 !== %d)\n", logic'(out));
         $stop;
      end
   end
endmodule
