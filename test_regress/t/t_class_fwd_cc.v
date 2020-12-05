// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

package Pkg;
   typedef class Fwd;
   virtual class Virt;
      pure virtual function Fwd get_root();
   endclass
   class Ext extends Virt;
      virtual function Fwd get_root();
         return Fwd::m_uvm_get_root();
      endfunction
   endclass
   class Fwd;
      function Fwd m_uvm_get_root();
         return null;
      endfunction
   endclass
endpackage
