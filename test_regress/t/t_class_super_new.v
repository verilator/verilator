// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

class Foo;
   int x;
   function new;
      this.x = 10;
   endfunction
endclass

class Bar extends Foo;
   function new;
      super.new;
   endfunction
endclass

class BarUnusedArg extends Foo;
   function new (int a);
      super.new;
   endfunction
endclass

class FooArg;
   int x;
   function new (int a);
      this.x = a;
   endfunction
endclass

class BarArg extends FooArg;
   function new (int a);
      super.new(a);
   endfunction
endclass

class BarExpr extends FooArg;
   function new (int a, string b);
      super.new(a + b.len());
   endfunction
endclass

class Foo2Args;
   int x;
   function new (int a, int b);
      this.x = a + b;
   endfunction
endclass

class Bar2Args extends Foo2Args;
   function new (int a, int b);
      super.new(a, b);
   endfunction
endclass

module t (/*AUTOARG*/
   );

   class FooInModule;
      int x;
      function new;
         this.x = 15;
      endfunction
   endclass

   class BarInModule extends FooInModule;
      function new;
         super.new;
      endfunction
   endclass

   Bar bar;
   BarInModule barInModule;
   BarUnusedArg barUnusedArg;
   BarArg barArg;
   BarExpr barExpr;
   Bar2Args bar2Args;

   initial begin
      bar = new;
      `checkh(bar.x, 10);
      barInModule = new;
      `checkh(barInModule.x, 15);
      barUnusedArg = new(2);
      `checkh(barUnusedArg.x, 10);
      barArg = new(2);
      `checkh(barArg.x, 2);
      barExpr = new (7, "ABCDEFGHI");
      `checkh(barExpr.x, 16);
      bar2Args = new(2, 12);
      `checkh(bar2Args.x, 14);

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
