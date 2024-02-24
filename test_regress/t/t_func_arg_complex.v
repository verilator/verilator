// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

class Cls;
   enum { ONEK = 1000, TWOK = 2000 } sev_t;
   int m_default_data;
   function int trigger(int data=get_default_data());
      return data;
   endfunction

   task triggert(output int o, input int data=get_default_data());
      o = data;
   endtask

   virtual function int get_default_data();
      return m_default_data;
   endfunction

   function int uvm_report(int severity,
                           int verbosity = (severity == 1) ? ONEK : TWOK);
      return verbosity;
   endfunction

endclass

module t(/*AUTOARG*/);

   function int mod_trigger(int data=mod_data());
      return data;
   endfunction

   task mod_triggert(output int o, input int data=mod_data());
      o = data;
   endtask

   int mod_default_data;
   function int mod_data();
      return mod_default_data;
   endfunction

   int v;

   initial begin
      begin
         mod_triggert(v, 1234);
         `checkd(v, 1234);

         mod_default_data = 42;
         v = mod_trigger();
         `checkd(v, 42);
         v = mod_trigger(11);
         `checkd(v, 11);
         mod_default_data = 43;
         v = mod_trigger();
         `checkd(v, 43);
         v = mod_trigger();  // Multiple to test look up of duplicates
         `checkd(v, 43);

         mod_default_data = 52;
         mod_triggert(v);
         `checkd(v, 52);
         mod_triggert(v);  // Multiple to test look up of duplicates
         `checkd(v, 52);
      end
      begin
         Cls c = new;

         c.m_default_data = 42;
         v = c.trigger();
         `checkd(v, 42);
         v = c.trigger(11);
         `checkd(v, 11);
         c.m_default_data = 43;
         v = c.trigger();
         `checkd(v, 43);
         v = c.trigger();  // Multiple to test look up of duplicates
         `checkd(v, 43);
         v = c.trigger();  // Multiple to test look up of duplicates
         `checkd(v, 43);

         c.m_default_data = 52;
         c.triggert(v);
         `checkd(v, 52);
         c.triggert(v);  // Multiple to test look up of duplicates
         `checkd(v, 52);

         v = c.uvm_report(1);
         `checkd(v, 1000);
         v = c.uvm_report(2);
         `checkd(v, 2000);
         v = c.uvm_report(1, 111);
         `checkd(v, 111);
         v = c.uvm_report(1, 222);
         `checkd(v, 222);
      end

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
