// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

   logic my_vec [4];
   logic bool;
   int count;

   initial begin
      my_vec = '{1, 0, 1, 0};
      count = $countones(my_vec);  // Bad, must be bit vector
      count = $countbits(my_vec, '0);  // Bad, must be bit vector
      bool = $onehot(my_vec);  // Bad, must be bit vector
      bool = $onehot0(my_vec);  // Bad, must be bit vector
      bool = $isunknown(my_vec);  // Bad, must be bit vector
      $stop;
   end

endmodule
