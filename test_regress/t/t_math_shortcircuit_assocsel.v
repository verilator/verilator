// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
   logic [31:0] dict [int];
   // verilator lint_off WIDTHTRUNC
   function automatic logic f(int a);
      int dict_size = dict.size;
      logic next_exists = dict.next(a);
      // incorrectly inserts element at `a`
      logic next_nonzero = !next_exists || (dict[a] != 0);
      if (dict_size != dict.size) begin
         $display("Assertion failed: dict_size mismatch");
         $display("Initial size: %0d, New size: %0d", dict_size, dict.size);
         $display("Dictionary contents:");
         foreach (dict[key]) begin
            $display(" Key: %0d, Value: %0d", key, dict[key]);
         end
         $error;
      end
      return next_nonzero;
   endfunction
   initial begin
      logic r = f(0);
      $display(r);
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
