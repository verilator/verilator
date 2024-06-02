// DESCRIPTION: Verilator: Check that an abstract class' contstructor
// can be called indirectly from a constructor of a derived class.
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Ilya Barkov
// SPDX-License-Identifier: CC0-1.0

// It's illegal to call
//     VBase b = new;
// see t_class_virtual_bad
virtual class VBase;
   function new(); endfunction
endclass

// Another constructor of an abstact class in the chain
virtual class VChild1 extends VBase;
   function new();
      super.new();
   endfunction
endclass

// It shall be perfectly fine to create an instance of a
// non-abstract VChild2
class VChild2 extends VChild1;
   function new();
      super.new();
   endfunction
endclass

module t;
   initial begin
      VChild2 c = new;
   end
endmodule
