// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0


class Cls;
   function int fi();
      return 10;
   endfunction
   function void fv();
   endfunction
   task t();
   endtask
   static function int sfi();
      return 10;
   endfunction
   static function void sfv();
   endfunction
   static task st();
   endtask
endclass

module t (/*AUTOARG*/);

   function int mod_fi();
      return 10;
   endfunction
   function void mod_fv();
   endfunction
   task mod_t();
   endtask

   initial begin
      Cls c;
      c = new;

      // For test of calling function in void context, see t_func_void_bad.v

      // Module
      if (mod_fi() != 10) $stop;  // OK
      void'(mod_fi());  // OK

      mod_fv();  // Warn IGNOREDRETURN
      void'(mod_fv());  // OK
      if (mod_fv() == 10) $stop;  // Bad call of task as function

      mod_t();  // OK
      if (mod_t() == 10) $stop;  // Bad call of task as function

      // Member functions
      if (c.fi() != 10) $stop;  // OK
      void'(c.fi());  // OK

      c.fv();  // Ok
      void'(c.fv());  // OK
      if (c.fv() == 10) $stop;  // Bad

      c.t();  // OK
      if (c.t() == 10) $stop;  // Bad

      // Static member functions
      if (c.sfi() != 10) $stop;  // OK
      void'(c.sfi());  // OK

      c.sfv();  // Ok
      void'(c.sfv());  // OK
      if (c.sfv() == 10) $stop;  // Bad

      c.st();  // OK
      if (c.st() == 10) $stop;  // Bad

      $stop;
   end
endmodule
