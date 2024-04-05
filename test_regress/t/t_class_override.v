// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Function names correspond to how the function is declared in the base class,
// then the extend class, with letters:
//   Does-not-exist(x), Nothing(n), :initial(i), :extends(e), :final(f)

class Base;
   // _X = non-existant
   // _n = None
   function int get_n; return 1; endfunction
   function int get_n_n; return 1; endfunction
   function int get_n_e; return 1; endfunction
   function int get_n_ef; return 1; endfunction
   function int get_n_i; return 1; endfunction
   function int get_n_if; return 1; endfunction
   function int get_n_f; return 1; endfunction
   // _e = :extends
   // function :extends int get_e; return 1; endfunction  // Bad
   // _ef = :extends :final
   // function :extends :final int get_ef; return 1; endfunction  // Bad
   // _i = :initial
   function :initial int get_i; return 1; endfunction
   function :initial int get_i_n; return 1; endfunction
   function :initial int get_i_e; return 1; endfunction
   function :initial int get_i_ef; return 1; endfunction
   function :initial int get_i_i; return 1; endfunction
   function :initial int get_i_if; return 1; endfunction
   function :initial int get_i_f; return 1; endfunction
   // _if = :initial :final
   function :initial :final int get_if; return 1; endfunction
   function :initial :final int get_if_n; return 1; endfunction
   function :initial :final int get_if_e; return 1; endfunction
   function :initial :final int get_if_ef; return 1; endfunction
   function :initial :final int get_if_i; return 1; endfunction
   function :initial :final int get_if_if; return 1; endfunction
   function :initial :final int get_if_f; return 1; endfunction
   // _f = :final
   function :final int get_f; return 1; endfunction
   function :final int get_f_n; return 1; endfunction
   function :final int get_f_e; return 1; endfunction
   function :final int get_f_ef; return 1; endfunction
   function :final int get_f_i; return 1; endfunction
   function :final int get_f_if; return 1; endfunction
   function :final int get_f_f; return 1; endfunction

endclass

class Cls extends Base;
   // _X = non-existant
   function int get_x_n; return 1; endfunction
   // function :extends int get_x_e; return 1; endfunction  // Bad
   // function :extends :final int get_x_ef; return 1; endfunction  // Bad
   function :initial int get_x_i; return 1; endfunction
   function :initial :final int get_x_if; return 1; endfunction
   function :final int get_x_f; return 1; endfunction
   // _n = None
   function int get_n_n; return 1; endfunction
   function :extends int get_n_e; return 1; endfunction
   function :extends :final int get_n_ef; return 1; endfunction
   // function :initial int get_n_i; return 1; endfunction  // Bad
   // function :initial :final int get_n_if; return 1; endfunction  // Bad
   function :final int get_n_f; return 1; endfunction
   // _e = :extends
   // _ef = :extends :final
   // _i = :initial
   function int get_i_n; return 1; endfunction
   function :extends int get_i_e; return 1; endfunction
   function :extends :final int get_i_ef; return 1; endfunction
   // function :initial int get_i_i; return 1; endfunction  // Bad
   // function :initial :final int get_i_if; return 1; endfunction  // Bad
   function :final int get_i_f; return 1; endfunction
   // _if = :initial :final
   // function int get_if_n; return 1; endfunction  // Bad
   // function :extends int get_if_e; return 1; endfunction  // Bad
   // function :extends :final int get_if_ef; return 1; endfunction  // Bad
   // function :initial int get_if_i; return 1; endfunction  // Bad
   // function :initial :final int get_if_if; return 1; endfunction  // Bad
   // function :final int get_if_f; return 1; endfunction  // Bad
   // _f = :final
   // function int get_f_n; return 1; endfunction  // Bad
   // function :extends int get_f_e; return 1; endfunction  // Bad
   // function :extends :final int get_f_ef; return 1; endfunction  // Bad
   // function :initial int get_f_i; return 1; endfunction  // Bad
   // function :initial :final int get_f_if; return 1; endfunction  // Bad
   // function :final int get_f_f; return 1; endfunction  // Bad
endclass

class CBase;
endclass

class CClsN extends CBase;
endclass

class :final CClsF extends CBase;
endclass

module t (/*AUTOARG*/);
   initial begin
      Cls c;
      CClsF cc;

      if (c != null) $stop;
      c = new;
      cc = new;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
