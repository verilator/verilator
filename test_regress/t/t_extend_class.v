// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003-2007 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Although strange, Verilog defines are expanded inside the C blocks
// (as the `systemc_* directives are opaque to the preprocessor)
`define finished "*-* All Finished *-*\n"

class Cls;
`ifdef verilator
 `systemc_header
#define DID_INT_HEADER 1
 `systemc_header_post
inline void `systemc_class_name::my_inline_function() {}
 `systemc_interface
#ifndef DID_INT_HEADER
#error "`systemc_header didn't work"
#endif
   bool m_did_ctor;
   uint32_t my_function() {
       if (!m_did_ctor) vl_fatal(__FILE__, __LINE__, __FILE__, "`systemc_ctor didn't work");
       return 1;
   }
   static void my_imp_function();
   static void my_inline_function();

 `systemc_imp_header
#define DID_IMP_HEADER 1
 `systemc_implementation

   void `systemc_class_name::my_imp_function() { }

 `systemc_ctor  // Works, but using a $c inside a `function new` might be cleaner
   m_did_ctor = 1;
 `systemc_dtor
   printf("In systemc_dtor\n");
   printf(`finished);
 `verilog

`endif  // verilator

endclass

module t (/*AUTOARG*/);

   int i;

   initial begin
      Cls c;
      c = new;
      i = $c(c, "->my_function()");
      $c(c, "->my_imp_function();");
      $c(c, "->my_inline_function();");
      c = null;  // Causes destruction and All Finished
      $finish;
   end

endmodule
