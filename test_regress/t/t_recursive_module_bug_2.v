// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2022 by Geza Lore. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.

module a #(parameter N) ();
   generate if (N > 1) begin
      // With N == 5, this will first expand N == 2, then expand N == 3,
      // which instantiates N == 2. This requires fixing up topological order
      // in V3Param.
      a #(.N(  N/2)) sub_lo();
      a #(.N(N-N/2)) sub_hi();
   end
   endgenerate
endmodule

module top();
   a #(.N(5)) root ();
endmodule
