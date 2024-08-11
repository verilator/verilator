// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Base;
endclass

class Cls extends Base;
   typedef int txn_type_t;  // Bad type

   rand txn_type_t req_txn_type;

   static function txn_type_t generate_txn();
      txn_type_t txn = new;
      txn_type_t copy = new txn;
      return txn;
   endfunction

endclass

module t(/*AUTOARG*/);

   initial begin
      Base b = Cls::generate_txn();
      $display("%p", b);

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
