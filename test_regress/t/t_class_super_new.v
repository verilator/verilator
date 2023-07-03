// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
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

class BarArgWithReturnInIf extends FooArg;
   function new (int a);
      super.new(a);
      if (a < 10) begin
         return;
      end
      this.x = 20;
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

class OptArgInNew;
   int x;
   function new (int y=1);
      x = y;
   endfunction
endclass

class NoNew extends OptArgInNew;
endclass

class NewWithoutSuper extends OptArgInNew;
   function new;
   endfunction
endclass

class OptArgInNewParam #(parameter int P=1);
   int x;
   function new (int y=1);
      x = y;
   endfunction
endclass

class NoNewParam#(parameter int R) extends OptArgInNewParam#(R);
endclass

class NewWithoutSuperParam#(parameter int R) extends OptArgInNewParam#();
   function new;
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
   NoNew noNew;
   NewWithoutSuper newWithoutSuper;
   NoNewParam#(2) noNewParam;
   NewWithoutSuperParam#(1) newWithoutSuperParam;
   BarArgWithReturnInIf barIf1, barIf10;

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
      noNew = new;
      `checkh(noNew.x, 1);
      newWithoutSuper = new;
      `checkh(newWithoutSuper.x, 1);
      noNewParam = new;
      `checkh(noNewParam.x, 1);
      newWithoutSuperParam = new;
      `checkh(newWithoutSuperParam.x, 1);
      barIf1 = new(1);
      `checkh(barIf1.x, 1);
      barIf10 = new(10);
      `checkh(barIf10.x, 20);

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
